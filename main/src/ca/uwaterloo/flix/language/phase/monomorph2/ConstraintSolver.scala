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
import ca.uwaterloo.flix.language.phase.monomorph2.ConstraintCollection.lowerChannelType
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.Defs
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.util.InternalCompilerException

import scala.collection.mutable

/**
  * Solves the flow constraints produced by [[ConstraintCollection]] to a fixpoint: starting from
  * the ground (all-constant) flows, each newly solved tuple is substituted into the flows that
  * depend on it until no new tuples appear. Sig destinations are additionally dispatched to their
  * implementing (or default) def. The result is, per polymorphic symbol, the set of ground
  * type-argument tuples it must be specialized at.
  */
object ConstraintSolver {

  /**
    * Solves `flows` to a fixpoint and returns the set of required specializations.
    *
    * Callers must run [[NonMonomorphizableCheck.checkMonomorphizable]] first; without it, a
    * non-monomorphizable flow set makes the fixpoint loop grow without bound.
    */
  def solve(flows: Set[Flow], root: TypedAst.Root)(implicit flix: Flix): Solution = flix.phase("ConstraintSolver") {
    val instanceMap = MonomorphCanon.mkInstanceMap(root.instances)
    val prepared    = flows.iterator.map(f => prepareFlow(f, root)).toList
    val dependents  = buildDependents(prepared)

    // The @LoweringTargetChannel defs are looked up by SolutionLowering with a type already run
    // through lowerType (Sender[t]/Receiver[t] rewritten to Mpmc[t, IO]), so their tuples must
    // get the same rewrite here — but only here: applying it in typeToMonoArg would corrupt the
    // keys of ordinary defs (e.g. Channel.send) whose own key keeps Sender/Receiver.
    val channelDefs = Set(Defs.ChannelGet, Defs.ChannelPut, Defs.ChannelNewTuple, Defs.ChannelMpmcAdmin, Defs.ChannelUnsafeGetAndUnlock)

    val solution  = mutable.Map.empty[MonoVar, mutable.Set[List[Type]]]
    val inFlight  = mutable.Set.empty[(MonoVar, List[Type])]
    val worklist  = mutable.Queue.empty[(MonoVar, List[Type])]

    def enqueue(dst: MonoVar, tuple0: List[Type]): Unit = {
      val tuple = dst match {
        case MonoVar.Def(sym) if channelDefs.contains(sym) => tuple0.map(lowerChannelType)
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
          case MonoVar.Sig(sigSym) =>
            resolveSig(sigSym, tuple, root, instanceMap).foreach {
              case (implSym, implArgs) => enqueue(MonoVar.Def(implSym), implArgs)
            }
          case _ => ()
        }

        // Propagate: substitute this MonoVar's new tuple into all dependent flows.
        for (pf <- dependents.getOrElse(dst, Nil)) {
          collapseArgsPrepared(pf, Map(dst -> tuple), root).foreach(groundTuple => enqueue(pf.dst, groundTuple))
        }
      }
    }

    Solution(
      defs = solution.collect { case (MonoVar.Def(sym), tuples) => sym -> tuples.toSet }.toMap,
      enums = solution.collect { case (MonoVar.Enum(sym), tuples) => sym -> tuples.toSet }.toMap,
      structs = solution.collect { case (MonoVar.Struct(sym), tuples) => sym -> tuples.toSet }.toMap,
      restrictableEnums = solution.collect { case (MonoVar.RestrictableEnum(sym), tuples) => sym -> tuples.toSet }.toMap
    )
  }(MonomorphDebug.DebugSolution)

  /** For each MonoVar, the set of (prepared) flows whose args contain `Param(mvar, _)`. */
  private def buildDependents(flows: List[PreparedFlow]): Map[MonoVar, List[PreparedFlow]] = {
    val m = mutable.Map.empty[MonoVar, mutable.ListBuffer[PreparedFlow]]
    for (pf <- flows) {
      val mvars = pf.args.flatMap(arg => MonoArg.collectParams(arg)).map(_._1).toSet
      for (v <- mvars) {
        m.getOrElseUpdate(v, mutable.ListBuffer.empty) += pf
      }
    }
    m.map { case (k, buf) => k -> buf.toList }.toMap
  }

  /**
    * Assembles a plain (possibly non-ground) `Type` from `arg`: `Param(v, i)` becomes
    * `bindings(v)(i)`, or `None` if `v` has no (long enough) tuple yet — "not ready, try again
    * later". No defaulting or canonicalization happens here; [[collapseArg]] does that once on
    * the whole assembled type.
    */
  private def assembleArg(arg: MonoArg, bindings: Map[MonoVar, List[Type]]): Option[Type] = arg match {
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

  /** Assembles every arg in `args`, or `None` if any is not ready. */
  private def assembleArgs(args: List[MonoArg], bindings: Map[MonoVar, List[Type]]): Option[List[Type]] = {
    val resolved = args.map(assembleArg(_, bindings))
    if (resolved.forall(_.isDefined)) Some(resolved.map(_.get)) else None
  }

  /**
    * Rewrites every `Region` constant in `t` to the `IO` effect — matches `StrictSubstitution`'s
    * treatment, applied everywhere since a region can already appear ground here.
    */
  private def rewriteRegionToIO(t: Type): Type = t match {
    case Type.Cst(TypeConstructor.Region(_), loc) => Type.Cst(TypeConstructor.Effect(Symbol.IO, Kind.Eff), loc)
    case Type.Apply(t1, t2, loc)                  => Type.Apply(rewriteRegionToIO(t1), rewriteRegionToIO(t2), loc)
    case Type.Alias(sym, args, inner, loc)        => Type.Alias(sym, args.map(rewriteRegionToIO), rewriteRegionToIO(inner), loc)
    case other                                    => other
  }

  /**
    * A flow with its Param-free arg positions collapsed once, up front: such a position collapses
    * to the same result on every tuple the flow is reconsidered for. `preCollapsed(i)` is
    * `Some(result)` for a Param-free position and `None` for one that must still be collapsed
    * per-tuple via `bindings`.
    */
  private case class PreparedFlow(dst: MonoVar, args: List[MonoArg], preCollapsed: List[Option[Option[Type]]])

  /** Returns `flow` with its Param-free positions pre-collapsed. */
  private def prepareFlow(flow: Flow, root: TypedAst.Root)(implicit flix: Flix): PreparedFlow = flow match {
    case Flow(args, dst) =>
      val preCollapsed = args.map { arg =>
        if (MonoArg.collectParams(arg).isEmpty) Some(collapseArg(arg, Map.empty, root))
        else None
      }
      PreparedFlow(dst, args, preCollapsed)
  }

  /** Collapses `pf`'s args to a ground tuple, or `None` if any position is not ready. */
  private def collapseArgsPrepared(pf: PreparedFlow, bindings: Map[MonoVar, List[Type]], root: TypedAst.Root)
                                   (implicit flix: Flix): Option[List[Type]] = {
    val resolved = pf.args.zip(pf.preCollapsed).map {
      case (_, Some(precomputed)) => precomputed
      case (arg, None)            => collapseArg(arg, bindings, root)
    }
    if (resolved.forall(_.isDefined)) Some(resolved.map(_.get)) else None
  }

  /**
    * Collapses `arg` to a ground type: assembles it (see [[assembleArg]]), then defaults and
    * canonicalizes via the shared [[MonomorphCanon]] pipeline, so the solver's collapsed type and
    * the specializer's instantiated type cannot structurally diverge for the same instantiation.
    * Returns `None` if the result remains non-ground — a solver gap, not an error, so it fails
    * soft. Defaulting a constrained `Star` var to `AnyType` is safe even when no instance exists:
    * `SolutionSpecialization.run` discards any speculative tuple whose reduction fails.
    */
  private def collapseArg(arg: MonoArg, bindings: Map[MonoVar, List[Type]], root: TypedAst.Root)
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

  /**
    * Resolves a sig call with type-arg `tuple` to the impl def sym and its type args.
    * Returns `None` if the instance cannot be found (e.g. for known gap cases).
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
