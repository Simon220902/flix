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
import ca.uwaterloo.flix.language.ast.{Kind, RigidityEnv, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.language.phase.monomorph.ConstraintCollection._
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.Defs
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import scala.collection.mutable

/**
  * Thrown when the flow set contains a "growing cycle" (see `ConstraintSolver.checkMonomorphizable`):
  * a recursive type that is provably wrapped in an additional type constructor on every cycle,
  * so no finite number of monomorphized copies can cover it (polymorphic recursion, e.g.
  * `def f(x: a): List[a] = ...f(lst)...`, or polymorphic packing/an escaping existential).
  *
  * Deliberately NOT an [[InternalCompilerException]] — this indicates a genuine property of the
  * user's program, not a compiler bug, even though (like `InternalCompilerException`) it is not
  * yet routed through the ordinary `CompilationMessage`/`Validation` error-reporting pipeline;
  * wiring that up properly is a separate, larger follow-up.
  */
case class NonMonomorphizableProgramException(message: String, loc: SourceLocation) extends RuntimeException(s"$message ($loc)")

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
    checkMonomorphizable(flows)

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

  // ---- Non-monomorphizable detection --------------------------------------------
  //
  // Polymorphic recursion (`def f(x: a): List[a] = ...f(lst)...`) and polymorphic packing
  // (an existential escaping into a recursive/cyclic flow) both mean the flow set has no finite
  // solution — the `while (worklist.nonEmpty)` loop above would otherwise just keep building
  // ever-larger types (`List[Int32]`, `List[List[Int32]]`, ...) until the JVM heap is exhausted.
  // Detected here, up front, per "The Simple Essence of Monomorphization" §3.3.2: reinterpret the
  // flow set as a graph over `(MVar, tuple-position)` vertices and look for a "growing cycle" — a
  // cycle that passes through at least one edge where the flowing type gets wrapped in an
  // additional type constructor. A cycle with only unwrapped (direct-copy) edges is ordinary,
  // convergent self-recursion and is fine. See `phases/3_constraint_solving/constraint_solving.md`
  // ("Future work: detecting non-monomorphizable programs") for the full derivation.
  //
  // Scoped to `MVar.Def`/`MVar.Sig` only (the only two kinds that end up in `Solution` / actually
  // drive specialized codegen — see `Solution.defs`'s `case (MVar.Def(sym), tuples) => ...` and
  // `resolveSig`'s dispatch-through-to-Def). `MVar.Enum`/`RestrictableEnum`/`Struct` positions are
  // intentionally excluded: this pipeline currently leaves enums/structs polymorphic (matching the
  // demand-driven baseline — "should enums be monomorphized?" is a separate, still-open design
  // question), so a *declared but never-instantiated* non-regular recursive enum (legitimate Flix
  // syntax, e.g. `enum T[a] { case Recurse(T[Wrap[a]]) }` with no runtime construction anywhere)
  // is inert to actual codegen and must not be rejected. Confirmed false positive without this
  // scoping: `Test.Dec.Enum.flix`'s `PolyRecursiveNonRegular`, declared only, never constructed.

  /** One tracked slot: the `pos`'th type-parameter position of `mvar`. */
  private case class Vertex(mvar: MVar, pos: Int)

  /** A graph edge: `src` flows into `dst`, `growing` iff it does so wrapped in a type constructor. */
  private case class Edge(src: Vertex, dst: Vertex, growing: Boolean)

  private def isTrackedForGrowth(mvar: MVar): Boolean = mvar match {
    case _: MVar.Def | _: MVar.Sig => true
    case _: MVar.Enum | _: MVar.RestrictableEnum | _: MVar.Struct => false
  }

  /**
    * Checks whether `flows` contains a growing cycle and throws [[NonMonomorphizableProgramException]]
    * if so. A no-op (and cheap: builds nothing) when there are no `Param`-carrying flows at all.
    */
  private def checkMonomorphizable(flows: Set[Flow]): Unit = {
    val edges: List[Edge] = flows.iterator.flatMap { case Flow(FlowInput.FlowArgs(args), dst) =>
      if (!isTrackedForGrowth(dst)) Iterator.empty
      else args.iterator.zipWithIndex.flatMap { case (arg, i) =>
        val dstV = Vertex(dst, i)
        arg match {
          // A bare, unwrapped Param: the type flows through unchanged — not growth.
          case MonoArg.Param(v, j) if isTrackedForGrowth(v) => List(Edge(Vertex(v, j), dstV, growing = false))
          // Anything else containing a Param (App/Assoc wrapping it, however deep) is growth —
          // EXCEPT effect/case-set algebra (Union, Intersection, Complement, Difference,
          // SymmetricDiff, and their Case-set analogs): those are bounded, idempotent set
          // operations over a finite universe of ground effects/cases, not generative recursive
          // data constructors, so wrapping a still-abstract polymorphic effect/region var in one
          // (e.g. a self-recursive call forwarding its own effect as `r + IO`) can never actually
          // diverge, unlike wrapping a value in `List[_]`. Confirmed false-positive without this
          // exclusion: `Fixpoint3.Phase.ProvenanceAugment.augmentOp`'s ordinary self-recursion
          // over a fixed, non-generic AST, region-polymorphic only in its effect `r`.
          case _ =>
            val growing = !isBoundedSetOp(arg)
            collectParamsWithIndex(arg).distinct.collect {
              case (v, j) if isTrackedForGrowth(v) => Edge(Vertex(v, j), dstV, growing = growing)
            }
        }
      }
    }.toList

    if (edges.isEmpty) return

    val vertices = edges.iterator.flatMap(e => Iterator(e.src, e.dst)).toSet
    val adjacency = edges.groupMap(_.src)(_.dst)
    val sccOf = stronglyConnectedComponents(vertices, adjacency)

    // A growing edge whose endpoints share an SCC necessarily lies on a cycle (by definition of
    // SCC, dst can reach src, so src -> dst -> ... -> src is a cycle through this growing edge).
    edges.find(e => e.growing && sccOf(e.src) == sccOf(e.dst)) match {
      case Some(edge) =>
        throw NonMonomorphizableProgramException(
          s"Program is not monomorphizable: found an infinitely-growing recursive type " +
          s"involving ${mvarLabel(edge.src.mvar)}. This indicates polymorphic recursion " +
          s"(e.g. `def f(x: a): List[a] = ...f(lst)...`) or an escaping existential " +
          s"(polymorphic packing) — Flix cannot generate a finite number of monomorphized " +
          s"copies for this definition.",
          mvarLoc(edge.src.mvar)
        )
      case None => ()
    }
  }

  /**
    * True iff `arg`'s outermost wrapping is an effect/case-set algebra operator (see the doc
    * comment above where this is used). Every argument position is uniformly one kind throughout
    * (Flix's kind system enforces this), so checking only the outermost head is sufficient — an
    * effect-kinded position can never have a `Kind.Star` data constructor mixed into it partway
    * down, or vice versa.
    */
  private def isBoundedSetOp(arg: MonoArg): Boolean = arg match {
    case MonoArg.App(MonoArg.Const(Type.Cst(tc, _)), _) => isSetAlgebraConstructor(tc)
    case _ => false
  }

  private def isSetAlgebraConstructor(tc: TypeConstructor): Boolean = tc match {
    case TypeConstructor.Union | TypeConstructor.Intersection | TypeConstructor.Complement |
         TypeConstructor.Difference | TypeConstructor.SymmetricDiff => true
    case _: TypeConstructor.CaseUnion | _: TypeConstructor.CaseIntersection |
         _: TypeConstructor.CaseComplement | _: TypeConstructor.CaseSymmetricDiff => true
    case _ => false
  }

  /** Every `(MVar, position)` pair reachable inside `arg`, however deeply wrapped. */
  private def collectParamsWithIndex(arg: MonoArg): List[(MVar, Int)] = arg match {
    case MonoArg.Const(_)          => Nil
    case MonoArg.Param(v, i)       => List((v, i))
    case MonoArg.App(tycon, args)  => collectParamsWithIndex(tycon) ++ args.flatMap(collectParamsWithIndex)
    case MonoArg.Assoc(_, a, _, _) => collectParamsWithIndex(a)
  }

  private def mvarLoc(mvar: MVar): SourceLocation = mvar match {
    case MVar.Def(sym)              => sym.loc
    case MVar.Enum(sym)             => sym.loc
    case MVar.Sig(sym)              => sym.loc
    case MVar.RestrictableEnum(sym) => sym.loc
    case MVar.Struct(sym)           => sym.loc
  }

  /**
    * Tarjan's strongly-connected-components algorithm. Returns a map from each vertex to an
    * arbitrary but consistent integer id shared by every vertex in its SCC (so two vertices are
    * mutually reachable iff they map to the same id).
    */
  private def stronglyConnectedComponents(vertices: Set[Vertex], adjacency: Map[Vertex, List[Vertex]]): Map[Vertex, Int] = {
    var nextIndex = 0
    val index    = mutable.Map.empty[Vertex, Int]
    val lowlink  = mutable.Map.empty[Vertex, Int]
    val onStack  = mutable.Set.empty[Vertex]
    val stack    = mutable.ArrayDeque.empty[Vertex]
    val sccId    = mutable.Map.empty[Vertex, Int]
    var nextScc  = 0

    def strongConnect(v: Vertex): Unit = {
      index(v) = nextIndex
      lowlink(v) = nextIndex
      nextIndex += 1
      stack.append(v)
      onStack += v

      for (w <- adjacency.getOrElse(v, Nil)) {
        if (!index.contains(w)) {
          strongConnect(w)
          lowlink(v) = math.min(lowlink(v), lowlink(w))
        } else if (onStack(w)) {
          lowlink(v) = math.min(lowlink(v), index(w))
        }
      }

      if (lowlink(v) == index(v)) {
        var w = stack.removeLast()
        onStack -= w
        sccId(w) = nextScc
        while (w != v) {
          w = stack.removeLast()
          onStack -= w
          sccId(w) = nextScc
        }
        nextScc += 1
      }
    }

    for (v <- vertices if !index.contains(v)) {
      strongConnect(v)
    }

    sccId.toMap
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
