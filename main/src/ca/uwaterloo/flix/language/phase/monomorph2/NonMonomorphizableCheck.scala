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
import ca.uwaterloo.flix.util.InternalCompilerException
import scala.collection.mutable

/**
  * Rejects non-monomorphizable programs (flow sets with no finite solution) before
  * [[ConstraintSolver.solve]]'s fixpoint loop, which would otherwise grow without bound.
  *
  * Following "The Simple Essence of Monomorphization" (§3.3.2), the flow set is reinterpreted as
  * a graph over `(MonoVar, tuple-position)` vertices, and we look for a "growing cycle": a reachable
  * cycle with at least one edge that wraps the flowing type in an additional type constructor
  * (`a` flowing into `List[a]`). Such a cycle arises from polymorphic recursion
  * (e.g. `def f(x: a): List[a] = f(x::Nil)`). A cycle of only direct-copy edges is
  * ordinary, convergent self-recursion and is fine.
  *
  * The check over-approximates in one known way: a non-regular enum whose growing case is declared
  * but never constructed is still rejected once any other case of it is constructed, even though
  * demand-driven specialization would not need the growing case.
  */
object NonMonomorphizableCheck {

  /** One tracked slot: the `pos`'th type-parameter position of `mvar`. */
  private case class Vertex(mvar: MonoVar, pos: Int)

  /** A graph edge: `src` flows into `dst`, `growing` iff it does so wrapped in a type constructor. */
  private case class Edge(src: Vertex, dst: Vertex, growing: Boolean)

  // TODO Make it a proper compiler error-message
  /**
    * Checks whether `flows` contains a reachable growing cycle and throws
    * [[InternalCompilerException]] if so.
    */
  def checkMonomorphizable(flows: Set[Flow]): Unit = {
    val edgesBuilder = List.newBuilder[Edge]
    val seedsBuilder = Set.newBuilder[Vertex]
    for (Flow(args, dst) <- flows) {
      for ((arg, i) <- args.zipWithIndex) {
        val dstV = Vertex(dst, i)
        arg match {
          case MonoArg.Param(v, j) =>
            edgesBuilder += Edge(Vertex(v, j), dstV, growing = false)
          case _ =>
            val ps = MonoArg.collectParams(arg).distinct
            if (ps.isEmpty)
              seedsBuilder += dstV
            else {
              val growing = isGrowingHead(arg)
              for ((v, j) <- ps)
                edgesBuilder += Edge(Vertex(v, j), dstV, growing = growing)
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

    // A growing edge whose endpoints share an SCC lies on a cycle.
    edges.find(e => e.growing && reachable(e.src) && sccOf(e.src) == sccOf(e.dst)) match {
      case Some(edge) =>
        throw InternalCompilerException(
          s"Program is not monomorphizable: found an infinitely-growing recursive type " +
          s"involving ${edge.src.mvar}. This indicates polymorphic recursion " +
          s"(e.g. `def f(x: a): List[a] = ...f(lst)...`) or a genuinely non-regular recursive " +
          s"enum/struct (e.g. `enum T[a] { case Base(a); case Recurse(T[Poly[a]]) }`) — Flix " +
          s"cannot generate a finite number of monomorphized copies for this definition.",
          monoVarLoc(edge.src.mvar)
        )
      case None => ()
    }
  }

  /**
    * Returns the vertices reachable from `seeds`.
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
    * Returns `true` iff `arg`'s outermost wrapping is growing, i.e. not an effect/case-set
    * algebra operator.
    */
  private def isGrowingHead(arg: MonoArg): Boolean = arg match {
    case MonoArg.App(MonoArg.Const(Type.Cst(tc, _)), _) => !isSetAlgebraConstructor(tc)
    case _ => true
  }

  /** Returns `true` iff `tc` is an effect or case-set algebra constructor. */
  private def isSetAlgebraConstructor(tc: TypeConstructor): Boolean = tc match {
    case TypeConstructor.Union | TypeConstructor.Intersection | TypeConstructor.Complement |
         TypeConstructor.Difference | TypeConstructor.SymmetricDiff => true
    case _: TypeConstructor.CaseUnion | _: TypeConstructor.CaseIntersection |
         _: TypeConstructor.CaseComplement | _: TypeConstructor.CaseSymmetricDiff => true
    case _ => false
  }

  /** Returns the source location of `mvar`'s declaration. */
  private def monoVarLoc(mvar: MonoVar): SourceLocation = mvar match {
    case MonoVar.Def(sym)              => sym.loc
    case MonoVar.Enum(sym)             => sym.loc
    case MonoVar.Sig(sym)              => sym.loc
    case MonoVar.RestrictableEnum(sym) => sym.loc
    case MonoVar.Struct(sym)           => sym.loc
  }

  /**
    * Tarjan's strongly-connected-components algorithm. Returns a map from each vertex to an
    * arbitrary but consistent integer id shared by every vertex in its SCC.
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
