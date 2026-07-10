/*
 * Copyright 2026 Simon Lykke Andersen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language.phase.monomorph2

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.{Kind, RigidityEnv, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.ast.shared.{RegionScope, SymUse}
import ca.uwaterloo.flix.language.dbg.AstPrinter
import ca.uwaterloo.flix.language.phase.monomorph2.ConstraintCollection._
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.Defs
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.util.tc.Debug
import ca.uwaterloo.flix.util.{FileOps, InternalCompilerException, ParOps}

import scala.collection.mutable

object ConstraintSolver {

  /**
    * The result of constraint solving: for each polymorphic def/enum/struct sym, the set of
    * concrete type argument tuples it must be specialised to. `enums`/`structs` are used by
    * `SolutionSpecialization` to emit genuinely specialized enum/struct declarations (fresh
    * symbols, renamed cases/fields) — see `Context.enumTable`/`structTable` there.
    * `RestrictableEnum` is deliberately not tracked here: unlike `EnumSym`/`StructSym`, it has no
    * `Symbol.freshRestrictableEnumSym` (no fresh-symbol infrastructure exists for it), so it
    * stays fully polymorphic, matching its pre-existing behavior.
    */
  case class Solution(
    defs: Map[Symbol.DefnSym, Set[List[Type]]],
    enums: Map[Symbol.EnumSym, Set[List[Type]]],
    structs: Map[Symbol.StructSym, Set[List[Type]]]
  )

  /**
    * Solves `flows` to a fixpoint and returns the set of required specializations.
    *
    * Callers must run `NonMonomorphizableCheck.checkMonomorphizable(flows)` first — this function
    * no longer does so itself (moved to its own top-level `flix.phase(...)` step in `Flix.scala`,
    * so its cost is visible separately from `ConstraintSolver`'s own timing rather than folded
    * into it). Without that precondition, a genuinely non-monomorphizable flow set makes this
    * function's fixpoint loop grow without bound instead of failing cleanly.
    */
  def solve(flows: Set[Flow], root: TypedAst.Root)(implicit flix: Flix): Solution = flix.phase("ConstraintSolver") {
    val instanceMap = MonomorphCanon.mkInstanceMap(root.instances)
    // Each flow's Param-free arg positions are collapsed here, ONCE, instead of on every tuple
    // the flow is ever reconsidered for (see prepareFlow's doc comment).
    val prepared    = flows.iterator.map(f => prepareFlow(f, root)).toList
    val dependents  = buildDependents(prepared)

    // The @LoweringTarget channel defs are queried by Lowering.mkGetChannel/mkPutChannel/
    // mkNewChannel with a type that has already been run through Lowering.lowerType (which
    // rewrites Sender[t]/Receiver[t] to Mpmc[t, IO]). Every other def's key comes from
    // subst(itpe), which never calls lowerType. So the rewrite must be applied here, at the
    // point tuples are computed for these three MVars specifically — not in typeToMonoArg, or
    // it would corrupt ordinary defs (e.g. Channel.send) whose own key keeps Sender/Receiver.
    val channelDefs = Set(Defs.ChannelGet, Defs.ChannelPut, Defs.ChannelNewTuple, Defs.ChannelMpmcAdmin, Defs.ChannelUnsafeGetAndUnlock)

    val solution  = mutable.Map.empty[MVar, mutable.Set[List[Type]]]
    val inFlight  = mutable.Set.empty[(MVar, List[Type])]
    val worklist  = mutable.Queue.empty[(MVar, List[Type])]

    def enqueue(dst: MVar, tuple0: List[Type]): Unit = {
      val tuple = dst match {
        case MVar.Def(sym) if channelDefs.contains(sym) => tuple0.map(lowerChannelType)
        case _                                          => tuple0
      }
      val key = (dst, tuple)
      if (!solution.get(dst).exists(_.contains(tuple)) && !inFlight.contains(key)) {
        inFlight += key
        worklist.enqueue((dst, tuple))
      }
    }

    // Seed: ground flows (all-Const args) become initial worklist entries.
    for (pf <- prepared) {
      collapseArgsPrepared(pf, Map.empty, root).foreach(tuple => enqueue(pf.dst, tuple))
    }

    // Fixpoint loop.
    while (worklist.nonEmpty) {
      val (dst, tuple) = worklist.dequeue()
      inFlight -= ((dst, tuple))

      val seen = solution.getOrElseUpdate(dst, mutable.Set.empty)
      if (!seen.contains(tuple)) {
        seen += tuple

        // Sig dispatch: resolve to impl def and forward the tuple.
        dst match {
          case MVar.Sig(sigSym) =>
            resolveSig(sigSym, tuple, root, instanceMap).foreach {
              case (implSym, implArgs) => enqueue(MVar.Def(implSym), implArgs)
            }
          case _ => ()
        }

        // Propagate: substitute this MVar's new tuple into all dependent flows.
        for (pf <- dependents.getOrElse(dst, Nil)) {
          collapseArgsPrepared(pf, Map(dst -> tuple), root).foreach(groundTuple => enqueue(pf.dst, groundTuple))
        }
      }
    }

    Solution(
      defs = solution.collect { case (MVar.Def(sym), tuples) => sym -> tuples.toSet }.toMap,
      enums = solution.collect { case (MVar.Enum(sym), tuples) => sym -> tuples.toSet }.toMap,
      structs = solution.collect { case (MVar.Struct(sym), tuples) => sym -> tuples.toSet }.toMap
    )
  }(DebugSolution)

  /** Plain-text listing of `solution`: summary stats, then every symbol's solved ground tuples,
    * grouped by category. Reuses `ConstraintCollection.mvarLabel`/its own type formatting so the
    * symbols read the same way they do in the flow dumps. */
  private def toText(solution: Solution): String = {
    def section[K](title: String, mk: K => MVar, m: Map[K, Set[List[Type]]]): String = {
      val lines = m.toList.map { case (k, tuples) =>
        s"${mvarLabel(mk(k))} -> ${tuples.toList.map(t => s"[${t.mkString(", ")}]").sorted.mkString(", ")}"
      }.sorted
      s"$title (${m.size} symbols, ${m.values.map(_.size).sum} tuples):\n" + lines.mkString("\n")
    }

    val header = List(
      s"total symbols: ${solution.defs.size + solution.enums.size + solution.structs.size}",
      s"total tuples: ${(solution.defs.values ++ solution.enums.values ++ solution.structs.values).map(_.size).sum}"
    ).mkString("\n")

    header + "\n\n" +
      section("Defs", MVar.Def(_), solution.defs) + "\n\n" +
      section("Enums", MVar.Enum(_), solution.enums) + "\n\n" +
      section("Structs", MVar.Struct(_), solution.structs) + "\n"
  }

  /**
    * Writes `solution` to `build/asts/monomorph2/ConstraintSolver.txt` under `--Xprint-phases`.
    * Bypasses `AstPrinter`'s shared `writeToDisk` (which hardcodes the `.flixir` extension for
    * every other phase) for the same reason `ConstraintCollection`'s own dumps do — a plain `.txt`
    * is more honest than `.flixir` for something that isn't one of the pipeline's ASTs.
    */
  private object DebugSolution extends Debug[Solution] {
    override def emit(name: String, solution: Solution)(implicit flix: Flix): Unit = {
      val dir = AstPrinter.astFolderPath.resolve("monomorph2")
      FileOps.writeString(dir.resolve("ConstraintSolver.txt"), toText(solution))
    }
  }

  // ---- Dependency index --------------------------------------------------------

  /** For each MVar, the set of (prepared) flows whose args contain `Param(mvar, _)`. */
  private def buildDependents(flows: List[PreparedFlow]): Map[MVar, List[PreparedFlow]] = {
    val m = mutable.Map.empty[MVar, mutable.ListBuffer[PreparedFlow]]
    for (pf <- flows) {
      for (v <- collectParamMVars(pf.args)) {
        m.getOrElseUpdate(v, mutable.ListBuffer.empty) += pf
      }
    }
    m.map { case (k, buf) => k -> buf.toList }.toMap
  }

  private def collectParamMVars(args: List[MonoArg]): Set[MVar] =
    args.flatMap(collectParamMVarsArg).toSet

  private def collectParamMVarsArg(arg: MonoArg): Set[MVar] = arg match {
    case MonoArg.Const(_)            => Set.empty
    case MonoArg.Param(v, _)         => Set(v)
    case MonoArg.App(tc, args)       => collectParamMVarsArg(tc) ++ args.flatMap(collectParamMVarsArg).toSet
    case MonoArg.Assoc(_, a, _, _)   => collectParamMVarsArg(a)
  }

  // ---- Arg collapse ------------------------------------------------------------

  /**
    * Assembles a plain (possibly non-ground) `Type` from `arg`'s `MonoArg` structure:
    * `Param(v, i)` becomes `bindings(v)(i)` (already fully resolved, from an earlier solved
    * tuple — returns `None` if `v` has no tuple yet, or not enough elements, i.e. "not ready,
    * try again later," which is not the same as a genuinely stray local var); `Const(t)` is
    * returned as-is, ground or not; `App`/`Assoc` nodes are structurally reassembled via
    * `Type.Apply`/`Type.AssocType`, unreduced. No defaulting or canonicalization happens here —
    * see `collapseArg`, which does that once, at the top, on the whole assembled type.
    */
  private def assembleArg(arg: MonoArg, bindings: Map[MVar, List[Type]]): Option[Type] = arg match {
    case MonoArg.Const(t) => Some(t)

    case MonoArg.Param(v, i) => bindings.get(v).flatMap { tup =>
      if (i < tup.length) Some(tup(i)) else None
    }

    case MonoArg.App(head, args) =>
      for {
        h  <- assembleArg(head, bindings)
        as <- assembleArgs(args, bindings)
      } yield as.foldLeft(h) { case (acc, t) => Type.Apply(acc, t, h.loc) }

    case MonoArg.Assoc(sym, a, kind, loc) =>
      assembleArg(a, bindings).map { t =>
        Type.AssocType(SymUse.AssocTypeSymUse(sym, loc), t, kind, loc)
      }
  }

  private def assembleArgs(args: List[MonoArg], bindings: Map[MVar, List[Type]]): Option[List[Type]] = {
    val resolved = args.map(assembleArg(_, bindings))
    if (resolved.forall(_.isDefined)) Some(resolved.map(_.get)) else None
  }

  /**
    * Rewrites every `Region` constant found anywhere in `t` to the `IO` effect — matches
    * `StrictSubstitution.apply`'s dedicated `Type.Cst(TypeConstructor.Region(_), _)` case,
    * applied everywhere (not just to stray vars), since a region can appear ground already
    * (e.g. forwarded via a `MonoArg.Param` from an earlier-solved tuple).
    */
  private def rewriteRegionToIO(t: Type): Type = t match {
    case Type.Cst(TypeConstructor.Region(_), loc) => Type.Cst(TypeConstructor.Effect(Symbol.IO, Kind.Eff), loc)
    case Type.Apply(t1, t2, loc)                  => Type.Apply(rewriteRegionToIO(t1), rewriteRegionToIO(t2), loc)
    case Type.Alias(sym, args, inner, loc)        => Type.Alias(sym, args.map(rewriteRegionToIO), rewriteRegionToIO(inner), loc)
    case other                                    => other
  }

  /**
    * A flow paired with a per-position precomputed collapse: each flow's `Params` all reference
    * the single enclosing decl's own MVar (see `ConstraintCollection`'s `Context`/`typeToMonoArg`),
    * so `bindings` (the other MVars' already-solved tuples) only ever affects Param-*containing*
    * arg positions — a Param-free position collapses to the exact same result on every tuple this
    * flow is ever reconsidered for. `preCollapsed(i)` is `Some(result)` for such a position
    * (computed once, here); `None` for a Param-containing position, which must still be collapsed
    * per-tuple via `bindings` in `collapseArgsPrepared`.
    *
    * A precomputed `Some(None)` (the arg exists but fails to collapse, e.g. an unreducible assoc
    * type) makes the whole flow permanently un-fireable — identical to today's per-tuple `None`
    * on every attempt, just computed once instead of repeatedly.
    */
  private case class PreparedFlow(dst: MVar, args: List[MonoArg], preCollapsed: List[Option[Option[Type]]])

  private def prepareFlow(flow: Flow, root: TypedAst.Root)(implicit flix: Flix): PreparedFlow = flow match {
    case Flow(FlowInput.FlowArgs(args), dst) =>
      val preCollapsed = args.map { arg =>
        if (collectParamMVarsArg(arg).isEmpty) Some(collapseArg(arg, Map.empty, root))
        else None
      }
      PreparedFlow(dst, args, preCollapsed)
  }

  private def collapseArgsPrepared(pf: PreparedFlow, bindings: Map[MVar, List[Type]], root: TypedAst.Root)
                                   (implicit flix: Flix): Option[List[Type]] = {
    val resolved = pf.args.zip(pf.preCollapsed).map {
      case (_, Some(precomputed)) => precomputed
      case (arg, None)            => collapseArg(arg, bindings, root)
    }
    if (resolved.forall(_.isDefined)) Some(resolved.map(_.get)) else None
  }

  /**
    * Collapses `arg` to a ground type: assembles it into a plain `Type` (see `assembleArg`), then
    * defaults and canonicalizes it, once, via the shared `MonomorphCanon` pipeline — the same
    * `simplify`/`default` calls `StrictSubstitution` uses when specializing, so the solver's
    * collapsed type and the specializer's instantiated type cannot structurally diverge for the
    * same instantiation.
    *
    * `default` defaults `Star`-kinded stray vars unconditionally (e.g. `AnyType`), even though a
    * `Star`-kinded type parameter can carry a trait constraint (`with Trait[t]`) that `AnyType`
    * doesn't satisfy — unlike the other defaulted kinds, this isn't always sound. What makes it
    * safe here regardless: `SolutionSpecialization.run`'s `entries` construction (see the
    * `InternalCompilerException` catch there) discards, per-tuple, any speculative specialization
    * this produces that turns out to need an instance that doesn't exist — same outcome as "the
    * solver never proposed this tuple," just discovered by attempting the real reduction instead
    * of predicting it up front.
    *
    * Returns `None` if `arg` remains non-ground after defaulting (e.g. a stray var of a kind
    * `default` doesn't resolve, or a reduction that legitimately doesn't apply here yet — a solver
    * gap, not an error, so it fails soft rather than throwing).
    */
  private def collapseArg(arg: MonoArg, bindings: Map[MVar, List[Type]], root: TypedAst.Root)
                          (implicit flix: Flix): Option[Type] =
    assembleArg(arg, bindings).flatMap { raw =>
      val defaulted = rewriteRegionToIO(raw).map(MonomorphCanon.default)
      try {
        val result = MonomorphCanon.simplify(defaulted, isGround = true)(root, flix)
        if (result.typeVars.nonEmpty) None else Some(result)
      } catch {
        case _: InternalCompilerException => None
      }
    }

  // ---- Sig dispatch ------------------------------------------------------------

  /**
    * Resolves a sig call with type-arg `tuple` to the impl def sym and its type args.
    * Returns None if the instance cannot be found (e.g. for known gap cases).
    */
  private def resolveSig(
    sigSym: Symbol.SigSym,
    tuple: List[Type],
    root: TypedAst.Root,
    instanceMap: Map[(Symbol.TraitSym, TypeConstructor), TypedAst.Instance]
  )(implicit flix: Flix): Option[(Symbol.DefnSym, List[Type])] = {
    if (tuple.isEmpty) return None

    val traitType = tuple.head
    val tyCon     = traitType.typeConstructor.getOrElse(return None)
    val instance  = instanceMap.getOrElse((sigSym.trt, tyCon), return None)
    val implDef   = instance.defs.find(_.sym.text == sigSym.name).getOrElse {
      // Sig has a default impl; synthesise a sym for the trait-level def.
      val sig = root.sigs(sigSym)
      sig.exp match {
        case None => return None
        case Some(_) =>
          val ns = sig.sym.trt.namespace :+ sig.sym.trt.name
          val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
          // The default impl belongs to the trait, not the instance, so it forwards the full sig
          // tuple as-is rather than the instance's tparam values — but the instantiation still
          // has to be checked for validity, the same way the non-default path below does.
          val _ = instanceArgsFor(instance, traitType, root).getOrElse(return None)
          return Some((defnSym, tuple))
      }
    }

    val instanceArgs = instanceArgsFor(instance, traitType, root).getOrElse(return None)
    val sigOwnArgs   = tuple.tail // type args beyond the trait type param
    Some((implDef.sym, instanceArgs ++ sigOwnArgs))
  }

  /**
    * Unifies `instance`'s declared type against `traitType` (the sig call's own trait-type-param
    * argument) and returns the resulting values of `instance`'s type params, in order. `None` if
    * the instantiation doesn't unify or leaves some instance type param unresolved.
    */
  private def instanceArgsFor(instance: TypedAst.Instance, traitType: Type, root: TypedAst.Root)
                              (implicit flix: Flix): Option[List[Type]] =
    if (instance.tparams.isEmpty) Some(Nil)
    else ConstraintSolver2.fullyUnify(instance.tpe, traitType, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix).flatMap { subst =>
      val args = instance.tparams.map(tp => subst.m.get(tp.sym))
      if (args.exists(_.isEmpty)) None else Some(args.map(_.get))
    }
}
