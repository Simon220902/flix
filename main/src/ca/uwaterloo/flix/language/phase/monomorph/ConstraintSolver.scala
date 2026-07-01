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

package ca.uwaterloo.flix.language.phase.monomorph

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.{Kind, RigidityEnv, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.language.phase.monomorph.ConstraintCollection._
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.Defs
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import scala.collection.mutable

object ConstraintSolver {

  /**
    * The result of constraint solving: for each polymorphic def sym, the set of concrete
    * type argument tuples it must be specialised to.
    */
  case class Solution(defs: Map[Symbol.DefnSym, Set[List[Type]]])

  /**
    * Solves `flows` to a fixpoint and returns the set of required specializations.
    */
  def solve(flows: Set[Flow], root: TypedAst.Root)(implicit flix: Flix): Solution = {
    val instanceMap = MonomorphCanon.mkInstanceMap(root.instances)
    val dependents  = buildDependents(flows)

    val solution  = mutable.Map.empty[MVar, mutable.Set[List[Type]]]
    val inFlight  = mutable.Set.empty[(MVar, List[Type])]
    val worklist  = mutable.Queue.empty[(MVar, List[Type])]

    // The @LoweringTarget channel defs are queried by Lowering.mkGetChannel/mkPutChannel/
    // mkNewChannel with a type that has already been run through Lowering.lowerType (which
    // rewrites Sender[t]/Receiver[t] to Mpmc[t, IO]). Every other def's key comes from
    // subst(itpe), which never calls lowerType. So the rewrite must be applied here, at the
    // point tuples are computed for these three MVars specifically — not in typeToMonoArg, or
    // it would corrupt ordinary defs (e.g. Channel.send) whose own key keeps Sender/Receiver.
    val channelDefs = Set(Defs.ChannelGet, Defs.ChannelPut, Defs.ChannelNewTuple, Defs.ChannelMpmcAdmin, Defs.ChannelUnsafeGetAndUnlock)

    def enqueue(dst: MVar, tuple0: List[Type]): Unit = {
      val tuple = dst match {
        case MVar.Def(sym) if channelDefs.contains(sym) => tuple0.map(lowerChannelType)
        case _                                          => tuple0
      }
      val key = (dst, tuple)
      if (!solution.getOrElse(dst, mutable.Set.empty).contains(tuple) && !inFlight.contains(key)) {
        inFlight += key
        worklist.enqueue((dst, tuple))
      }
    }

    // Seed: ground flows (all-Const args) become initial worklist entries.
    for (Flow(FlowInput.FlowArgs(args), dst) <- flows) {
      collapseArgs(args, Map.empty, root) match {
        case Some(tuple) => enqueue(dst, tuple)
        case None        => ()
      }
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
            resolveSig(sigSym, tuple, root, instanceMap) match {
              case Some((implSym, implArgs)) => enqueue(MVar.Def(implSym), implArgs)
              case None                      => ()
            }
          case _ => ()
        }

        // Propagate: substitute this MVar's new tuple into all dependent flows.
        for (Flow(FlowInput.FlowArgs(args), flowDst) <- dependents.getOrElse(dst, Nil)) {
          collapseArgs(args, Map(dst -> tuple), root) match {
            case Some(groundTuple) => enqueue(flowDst, groundTuple)
            case None              => ()
          }
        }
      }
    }

    Solution(solution.collect {
      case (MVar.Def(sym), tuples) => sym -> tuples.toSet
    }.toMap)
  }

  // ---- Dependency index --------------------------------------------------------

  /** For each MVar, the set of flows whose args contain `Param(mvar, _)`. */
  private def buildDependents(flows: Set[Flow]): Map[MVar, List[Flow]] = {
    val m = mutable.Map.empty[MVar, mutable.ListBuffer[Flow]]
    for (flow @ Flow(FlowInput.FlowArgs(args), _) <- flows) {
      for (v <- collectParamMVars(args)) {
        m.getOrElseUpdate(v, mutable.ListBuffer.empty) += flow
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

    case MonoArg.Assoc(sym, arg, kind, loc) =>
      assembleArg(arg, bindings).map { t =>
        Type.AssocType(ca.uwaterloo.flix.language.ast.shared.SymUse.AssocTypeSymUse(sym, loc), t, kind, loc)
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
    * Collapses `args` to ground types: assembles each into a plain `Type` (see `assembleArg`),
    * then defaults and canonicalizes each one, once, via the shared `MonomorphCanon` pipeline —
    * the same `simplify`/`default` calls `StrictSubstitution` uses when specializing, so the
    * solver's collapsed type and the specializer's instantiated type cannot structurally diverge
    * for the same instantiation.
    *
    * `default` defaults `Star`-kinded stray vars unconditionally (e.g. `AnyType`), even though a
    * `Star`-kinded type parameter can carry a trait constraint (`with Trait[t]`) that `AnyType`
    * doesn't satisfy — unlike the other defaulted kinds, this isn't always sound. What makes it
    * safe here regardless: `SolutionSpecialization.run`'s `entries` construction (see the
    * `InternalCompilerException` catch there) discards, per-tuple, any speculative
    * specialization this produces that turns out to need an instance that doesn't exist —
    * same outcome as "the solver never proposed this tuple," just discovered by attempting the
    * real reduction instead of predicting it up front. See
    * `notes/plan_canonicalization_unification.md` for the full argument.
    *
    * Returns `None` if any arg remains non-ground after defaulting (e.g. a stray var of a kind
    * `default` doesn't resolve, or a reduction that legitimately doesn't apply here yet — a
    * solver gap, not an error, so it fails soft rather than throwing).
    */
  private def collapseArgs(args: List[MonoArg], bindings: Map[MVar, List[Type]], root: TypedAst.Root)
                           (implicit flix: Flix): Option[List[Type]] = {
    val resolved = args.map(collapseArg(_, bindings, root))
    if (resolved.forall(_.isDefined)) Some(resolved.map(_.get)) else None
  }

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
          // Compute args for the default impl: instance tparam values ++ sig-own tparam values.
          // instanceArgs is computed below using the same unification path as the normal case.
          val instanceArgs: List[Type] =
            if (instance.tparams.isEmpty) Nil
            else
              ConstraintSolver2.fullyUnify(instance.tpe, traitType, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix) match {
                case None        => return None
                case Some(subst) =>
                  val args = instance.tparams.map(tp => subst.m.get(tp.sym))
                  if (args.exists(_.isEmpty)) return None
                  args.map(_.get)
              }
          // Default impl belongs to the trait, not an instance.
          // Its spec.tparams includes the trait tparam, so forward the full sig tuple.
          return Some((defnSym, tuple))
      }
    }

    // Compute impl-def arg tuple: instance-tparam values (from traitType) ++ sig-own tparam values.
    val instanceArgs: List[Type] =
      if (instance.tparams.isEmpty) Nil
      else
        ConstraintSolver2.fullyUnify(instance.tpe, traitType, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix) match {
          case None        => return None
          case Some(subst) =>
            val args = instance.tparams.map(tp => subst.m.get(tp.sym))
            if (args.exists(_.isEmpty)) return None
            args.map(_.get)
        }

    val sigOwnArgs = tuple.tail  // type args beyond the trait type param
    Some((implDef.sym, instanceArgs ++ sigOwnArgs))
  }
}
