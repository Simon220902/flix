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

import ca.uwaterloo.flix.language.ast.{SourceLocation, Type, TypeConstructor}
import ca.uwaterloo.flix.language.phase.monomorph2.ConstraintCollection._

import scala.collection.mutable

/**
  * Thrown when the flow set contains a "growing cycle" (see `NonMonomorphizableCheck.checkMonomorphizable`):
  * a recursive type that is provably wrapped in an additional type constructor on every cycle,
  * so no finite number of monomorphized copies can cover it. The two ways this happens in Flix:
  * polymorphic recursion (e.g. `def f(x: a): List[a] = ...f(lst)...`) or a genuinely non-regular
  * recursive enum/struct (e.g. `enum T[a] { case Base(a); case Recurse(T[Poly[a]]) }`).
  *
  * Deliberately NOT an [[ca.uwaterloo.flix.util.InternalCompilerException]] — this indicates a
  * genuine property of the user's program, not a compiler bug, even though (like
  * `InternalCompilerException`) it is not yet routed through the ordinary
  * `CompilationMessage`/`Validation` error-reporting pipeline; wiring that up properly is a
  * separate, larger follow-up.
  */
case class NonMonomorphizableProgramException(message: String, loc: SourceLocation) extends RuntimeException(s"$message ($loc)")

/**
  * Detects "non-monomorphizable" programs — flow sets with no finite solution — before `solve`'s
  * fixpoint loop runs, so that a genuinely divergent program gets a clean rejection instead of an
  * uncontrolled OOM crash. Split out of `ConstraintSolver.scala` as its own self-contained
  * subsystem: a single entry point (`checkMonomorphizable`, called once from `solve`) plus a
  * small purpose-built graph (`Vertex`/`Edge`) derived from the flow set, used by nothing else in
  * the pipeline.
  */
object NonMonomorphizableCheck {

  // ---- Non-monomorphizable detection --------------------------------------------
  //
  // Polymorphic recursion (`def f(x: a): List[a] = ...f(lst)...`) and a genuinely non-regular
  // recursive enum/struct (e.g. `enum T[a] { case Base(a); case Recurse(T[Poly[a]]) }`) both mean
  // the flow set has no finite solution — the solver's `while (worklist.nonEmpty)` loop would
  // otherwise just keep building ever-larger types (`List[Int32]`, `List[List[Int32]]`, ...) until
  // the JVM heap is exhausted. Detected here, up front, per "The Simple Essence of
  // Monomorphization" §3.3.2: reinterpret the flow set as a graph over `(MVar, tuple-position)`
  // vertices and look for a "growing cycle" — a cycle that passes through at least one edge where
  // the flowing type gets wrapped in an additional type constructor. A cycle with only unwrapped
  // (direct-copy) edges is ordinary, convergent self-recursion and is fine. (The paper's own
  // presentation of this algorithm, written for a more general source language, also covers a
  // third case — an escaping existential/"polymorphic packing" — but Flix has no existential
  // types, so that case cannot actually arise here.) See
  // `phases/3_constraint_solving/constraint_solving.md` ("Detecting non-monomorphizable programs")
  // for the full derivation.
  //
  // Every `MVar` kind participates unconditionally (Def/Sig/Enum/RestrictableEnum/Struct) — there
  // is no per-kind opt-out. This matters even for `RestrictableEnum`, even though `Solution`
  // doesn't report solved tuples for it (no fresh-symbol infrastructure exists for
  // `Symbol.RestrictableEnumSym`, see `Solution`'s doc comment; it stays fully polymorphic).
  // Whether a kind is *reported* in the final `Solution` and whether it must be *checked here for
  // safety* are separate concerns: `visitType`'s `TypeConstructor.Enum`/`RestrictableEnum`/
  // `Struct` cases all emit real flows unconditionally, and the solver's
  // `while (worklist.nonEmpty)` loop propagates every flow uniformly regardless of destination
  // kind — it does not know or care whether the result is ever read or reported. A genuinely
  // non-regular recursive enum/struct/restrictable enum
  // (`enum T[a] { case Base(a); case Recurse(T[Wrap[a]]) }`) that is constructed anywhere in the
  // program makes the solver itself try to compute an unbounded sequence of tuples for its own
  // MVar — `[Int32]`, `[Wrap[Int32]]`, `[Wrap[Wrap[Int32]]]`, ... — and OOMs, independent of
  // whether anything downstream would have used (or could even report) the result. Confirmed by
  // direct repro: before `RestrictableEnum` was included here, a non-regular recursive
  // restrictable enum ran straight past this check and OOM'd the JVM heap ~2 minutes later inside
  // `Type.Apply.hashCode`, instead of getting the clean rejection below.
  //
  // This does over-approximate relative to what `Eraser` (and `SolutionSpecialization`, which
  // reuses the same solved tuples) can actually need: a genuinely non-regular recursive enum
  // whose "growing" case (`Recurse` above) is declared but never actually constructed anywhere
  // gets rejected by this check even though nothing downstream would need it (`Eraser` specializes
  // demand-driven, per actually-constructed case, so a `Base`-only program compiles fine there).
  // This is a known, accepted false positive — trading a rejection of a safe-but-structurally-
  // suspicious program for guaranteed avoidance of the OOM above. Reachability (below) still
  // correctly excludes the common, *actually*-benign case — a non-regular recursive enum that is
  // declared but never constructed anywhere at all (e.g. `Test.Dec.Enum.flix`'s
  // `PolyRecursiveNonRegular`) — since nothing ever seeds it. Closing the remaining gap precisely
  // would mean giving this check the same per-case demand-driven granularity `Eraser` already has
  // — a larger change, not done here.

  /** One tracked slot: the `pos`'th type-parameter position of `mvar`. */
  private case class Vertex(mvar: MVar, pos: Int)

  /** A graph edge: `src` flows into `dst`, `growing` iff it does so wrapped in a type constructor. */
  private case class Edge(src: Vertex, dst: Vertex, growing: Boolean)

  /**
    * Checks whether `flows` contains a growing cycle and throws [[NonMonomorphizableProgramException]]
    * if so. A no-op (and cheap: builds nothing) when there are no `Param`-carrying flows at all.
    */
  def checkMonomorphizable(flows: Set[Flow]): Unit = {
    // Edges and seeds are computed in one pass over each flow's args: a position's
    // `collectParamsWithIndex(arg)` result is needed for both the growing-edge classification and
    // the seed check (`.isEmpty`), so computing it once and reusing it avoids a redundant
    // structural walk over `arg`.
    val edgesBuilder = List.newBuilder[Edge]
    val seedsBuilder = Set.newBuilder[Vertex]
    for (Flow(FlowInput.FlowArgs(args), dst) <- flows) {
      for ((arg, i) <- args.zipWithIndex) {
        val dstV = Vertex(dst, i)
        arg match {
          // A bare, unwrapped Param: the type flows through unchanged — not growth, and (having
          // exactly one param dependency, itself) never a seed either way.
          case MonoArg.Param(v, j) =>
            edgesBuilder += Edge(Vertex(v, j), dstV, growing = false)
          // Anything else containing a Param (App/Assoc wrapping it, however deep) is growth —
          // EXCEPT effect/case-set algebra (Union, Intersection, Complement, Difference,
          // SymmetricDiff, and their Case-set analogs): those are bounded, idempotent set
          // operations over a finite universe of ground effects/cases, not generative recursive
          // data constructors, so wrapping a still-abstract polymorphic effect/region var in one
          // (e.g. a self-recursive call forwarding its own effect as `r + IO`) can never actually
          // diverge, unlike wrapping a value in `List[_]`. Without this exclusion, ordinary
          // self-recursion that is only effect-polymorphic (e.g.
          // `Fixpoint3.Phase.ProvenanceAugment.augmentOp`, region-polymorphic in its effect `r`
          // over an otherwise fixed, non-generic AST) would be misclassified as a growing cycle.
          case _ =>
            val ps = collectParamsWithIndex(arg).distinct
            if (ps.isEmpty) seedsBuilder += dstV
            else {
              val growing = !isBoundedSetOp(arg)
              for ((v, j) <- ps) edgesBuilder += Edge(Vertex(v, j), dstV, growing = growing)
            }
        }
      }
    }
    val edges = edgesBuilder.result()

    if (edges.isEmpty) return

    val adjacency = edges.groupMap(_.src)(_.dst)
    val reachable = reachableFromSeeds(seedsBuilder.result(), adjacency)
    val vertices = edges.iterator.flatMap(e => Iterator(e.src, e.dst)).toSet
    val sccOf = stronglyConnectedComponents(vertices, adjacency)

    // A growing edge whose endpoints share an SCC necessarily lies on a cycle (by definition of
    // SCC, dst can reach src, so src -> dst -> ... -> src is a cycle through this growing edge).
    // Restricting to `reachable(e.src)` is enough to restrict the whole check to reachable SCCs:
    // if `e.src` is reachable and `e.dst` is in the same SCC, `e.dst` (and everything else in
    // that SCC, including the path back to `e.src`) is reachable too, by construction of
    // `reachableFromSeeds` (a set closed under following edges forward).
    edges.find(e => e.growing && reachable(e.src) && sccOf(e.src) == sccOf(e.dst)) match {
      case Some(edge) =>
        throw NonMonomorphizableProgramException(
          s"Program is not monomorphizable: found an infinitely-growing recursive type " +
          s"involving ${mvarLabel(edge.src.mvar)}. This indicates polymorphic recursion " +
          s"(e.g. `def f(x: a): List[a] = ...f(lst)...`) or a genuinely non-regular recursive " +
          s"enum/struct (e.g. `enum T[a] { case Base(a); case Recurse(T[Poly[a]]) }`) — Flix " +
          s"cannot generate a finite number of monomorphized copies for this definition.",
          mvarLoc(edge.src.mvar)
        )
      case None => ()
    }
  }

  /**
    * Vertices reachable from `seeds`: each seed is a `(dst, i)` position targeted by some flow
    * whose `i`'th arg has no `Param` dependency at all (resolvable without needing any other
    * `MVar`'s tuple first — the same condition `solve`'s own seed loop uses via
    * `collapseArgsPrepared`, whose Param-free positions are exactly `prepareFlow`'s precomputed
    * ones). `seeds` is deliberately computed per-position by the caller (`checkMonomorphizable`)
    * rather than requiring the whole flow to be simultaneously ground (which is what real seeding
    * requires): a superset of what the solver would actually seed, which only makes this check
    * *more* likely to catch a real growing cycle, never less — the safe direction to be
    * approximate in, unlike under-approximating (which would silently let a real hang back
    * through, the exact failure mode this check exists to prevent).
    */
  private def reachableFromSeeds(seeds: Set[Vertex], adjacency: Map[Vertex, List[Vertex]]): Set[Vertex] = {
    val reachable = mutable.Set.empty[Vertex]
    val queue = mutable.Queue.empty[Vertex]
    reachable ++= seeds
    queue.enqueueAll(seeds)
    while (queue.nonEmpty) {
      val v = queue.dequeue()
      for (w <- adjacency.getOrElse(v, Nil) if !reachable(w)) {
        reachable += w
        queue.enqueue(w)
      }
    }
    reachable.toSet
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

}
