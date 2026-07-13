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
import ca.uwaterloo.flix.language.ast.TypedAst.*
import ca.uwaterloo.flix.language.ast.TypedAst.Predicate.{Body, Head}
import ca.uwaterloo.flix.language.ast.Symbol
import ca.uwaterloo.flix.language.dbg.AstPrinter.DebugTypedAst
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

/**
  * Tree-shakes `root`, pruning unreachable `root.defs`, `root.instances`, and `root.sigs`.
  *
  * Runs for both the constraint-based monomorphization pipeline and the demand-driven baseline,
  * superseding [[ca.uwaterloo.flix.language.phase.TreeShaker1]] (now dead code) in both:
  * `TreeShaker1` computes the same def/trait/sig reachability info this pass needs, but only
  * ever used it to prune `root.defs`.
  *
  * Pruning instances and sig bodies matters because `ConstraintCollection` — unlike the
  * demand-driven `Specialization.scala` — walks every instance implementation and default
  * trait-sig body unconditionally, regardless of whether it is ever actually dispatched to, and
  * its solver seeds any call found this way whose argument types are already concrete,
  * regardless of whether the surrounding declaration is reachable. Left unpruned, that
  * unconditional walk would specialize code no reachable call site can ever invoke.
  *
  * An instance is dropped entirely if its trait is never reached — the same trait-level
  * granularity `TreeShaker1` already uses when deciding which instances' bodies to walk for
  * transitive reachability, so this can keep a few genuinely-unused instances of an
  * otherwise-used trait, but never drops something still needed. A default sig implementation's
  * body is dropped if its own sig is never reached via `ApplySig`.
  */
object MonomorphTreeShaker {

  /** Performs tree shaking on `root`, additionally pruning unreached instances/default sig bodies. */
  def run(root: Root)(implicit flix: Flix): Root = flix.phase("MonomorphTreeShaker") {
    val initReach: Set[ReachableSym] = root.entryPoints.map(ReachableSym.DefnSym.apply)

    val defaultHandlers = root.defaultHandlers.map(handler => ReachableSym.DefnSym(handler.handlerSym)).toSet

    // Compute the symbols that are transitively reachable. `@LoweringTargetDatalog`/
    // `@LoweringTargetChannel` defs are pulled in lazily via the `ChannelUsed`/`DatalogUsed`
    // sentinels emitted by `visitExp` (see below), not seeded unconditionally, so a program using
    // neither feature keeps neither def group.
    val allReachable = ParOps.parReach(initReach ++ defaultHandlers, visitSym(_, root))

    // Filter the reachable definitions.
    val reachableDefs = root.defs.filter {
      case (sym, _) => allReachable.contains(ReachableSym.DefnSym(sym))
    }

    // Drop instances of traits that are never reached (same granularity TreeShaker1 already
    // uses internally when it decides which instances' bodies to walk).
    val reachableInstances = root.instances.filter {
      case (traitSym, _) => allReachable.contains(ReachableSym.TraitSym(traitSym))
    }

    // Drop unreached default sig implementations, keeping the (bodiless) sig declaration itself.
    val reachableSigs = root.sigs.map {
      case (sigSym, sig) if allReachable.contains(ReachableSym.SigSym(sigSym)) => sigSym -> sig
      case (sigSym, sig) => sigSym -> sig.copy(exp = None)
    }

    root.copy(defs = reachableDefs, instances = reachableInstances, sigs = reachableSigs)
  }

  /** Returns the symbols reachable from `sym`. */
  private def visitSym(sym: ReachableSym, root: Root): Set[ReachableSym] = sym match {
    case ReachableSym.DefnSym(defnSym) =>
      val defn = root.defs(defnSym)
      visitExp(defn.exp)

    case ReachableSym.SigSym(sigSym) =>
      val sig = root.sigs(sigSym)
      Set(ReachableSym.TraitSym(sig.sym.trt)) ++
        sig.exp.map(visitExp).getOrElse(Set.empty)

    case ReachableSym.TraitSym(traitSym) =>
      root.instances(traitSym).foldLeft(Set.empty[ReachableSym]) {
        case (acc, s) => visitExps(s.defs.map(_.exp)) ++ acc
      }

    // `Lowering` is what actually synthesizes call sites to `@LoweringTargetDatalog`/
    // `@LoweringTargetChannel` defs; ordinary reachability can't see those calls yet, so pull in
    // the whole triggered category here.
    case ReachableSym.ChannelUsed =>
      root.defs.values.filter(_.spec.ann.isLoweringTargetChannel)
        .map(d => ReachableSym.DefnSym(d.sym)).toSet

    case ReachableSym.DatalogUsed =>
      root.defs.values.filter(_.spec.ann.isLoweringTargetDatalog)
        .map(d => ReachableSym.DefnSym(d.sym)).toSet
  }

  /** Returns the symbols reachable from `e0`. */
  private def visitExp(e0: Expr): Set[ReachableSym] = e0 match {
    case Expr.Cst(_, _, _) =>
      Set.empty

    case Expr.Var(_, _, _) =>
      Set.empty

    case Expr.Hole(_, _, _, _, _) =>
      Set.empty

    case Expr.HoleWithExp(exp, _, _, _, _) =>
      visitExp(exp)

    case Expr.OpenAs(_, exp, _, _) =>
      visitExp(exp)

    case Expr.Use(_, _, exp, _) =>
      visitExp(exp)

    case Expr.Lambda(_, exp, _, _) =>
      visitExp(exp)

    case Expr.ApplyClo(exp1, exp2, _, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.ApplyDef(bnd, exps, _, _, _, _, _, _) =>
      Set(ReachableSym.DefnSym(bnd.sym)) ++ visitExps(exps)

    case Expr.ApplyLocalDef(_, exps, _, _, _, _, _) =>
      visitExps(exps)

    case Expr.ApplyOp(_, exps, _, _, _, _) =>
      visitExps(exps)

    case Expr.ApplySig(bnd, exps, _, _, _, _, _, _, _) =>
      Set(ReachableSym.SigSym(bnd.sym)) ++ visitExps(exps)

    case Expr.Unary(_, exp, _, _, _) =>
      visitExp(exp)

    case Expr.Binary(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Let(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.LocalDef(_, _, _, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Region(_, _, exp, _, _, _) =>
      visitExp(exp)

    case Expr.IfThenElse(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.Stm(exps, exp, _, _, _) =>
      exps.foldRight(visitExp(exp))((e, acc) => visitExp(e) ++ acc)

    case Expr.Discard(exp, _, _) =>
      visitExp(exp)

    case Expr.Match(exp, rules, _, _, _) =>
      visitExp(exp) ++ visitExps(rules.map(_.exp)) ++ visitExps(rules.flatMap(_.guard))

    case Expr.RestrictableChoose(_, exp, rules, _, _, _) =>
      visitExp(exp) ++ visitExps(rules.map(_.exp))

    case Expr.ExtMatch(exp, rules, _, _, _) =>
      visitExp(exp) ++ visitExps(rules.map(_.exp))

    case Expr.Tag(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.RestrictableTag(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.ExtTag(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.Tuple(exps, _, _, _) =>
      visitExps(exps)

    case Expr.RecordSelect(exp, _, _, _, _) =>
      visitExp(exp)

    case Expr.RecordExtend(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.RecordRestrict(_, exp, _, _, _) =>
      visitExp(exp)

    case Expr.ArrayLit(exps, exp, _, _, _) =>
      visitExps(exps) ++ visitExp(exp)

    case Expr.ArrayNew(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.ArrayLoad(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.ArrayLength(exp, _, _) =>
      visitExp(exp)

    case Expr.ArrayStore(exp1, exp2, exp3, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.StructNew(_, fields, region, _, _, _) =>
      visitExps(fields.map(_._2)) ++ region.map(visitExp).getOrElse(Set.empty)

    case Expr.StructGet(exp, _, _, _, _) =>
      visitExp(exp)

    case Expr.StructPut(exp1, _, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.VectorLit(exps, _, _, _) =>
      visitExps(exps)

    case Expr.VectorLoad(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.VectorLength(exp, _) =>
      visitExp(exp)

    case Expr.Ascribe(exp, _, _, _, _, _) =>
      visitExp(exp)

    case Expr.InstanceOf(exp, _, _) =>
      visitExp(exp)

    case Expr.CheckedCast(_, exp, _, _, _) =>
      visitExp(exp)

    case Expr.UncheckedCast(exp, _, _, _, _, _) =>
      visitExp(exp)

    case Expr.Unsafe(exp, _, _, _, _, _) =>
      visitExp(exp)

    case Expr.TryCatch(exp, rules, _, _, _) =>
      visitExp(exp) ++ visitExps(rules.map(_.exp))

    case Expr.Throw(exp, _, _, _) =>
      visitExp(exp)

    case Expr.Handler(_, rules, _, _, _, _, _) =>
      visitExps(rules.map(_.exp))

    case Expr.InvokeConstructor(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.InvokeSuperConstructor(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.InvokeMethod(_, exp, exps, _, _, _) =>
      visitExp(exp) ++ visitExps(exps)

    case Expr.InvokeSuperMethod(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.InvokeStaticMethod(_, exps, _, _, _) =>
      visitExps(exps)

    case Expr.GetField(_, exp, _, _, _) =>
      visitExp(exp)

    case Expr.PutField(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.GetStaticField(_, _, _, _) =>
      Set.empty

    case Expr.PutStaticField(_, exp, _, _, _) =>
      visitExp(exp)

    case Expr.NewObject(_, _, _, _, constructors, methods, _) =>
      visitExps(constructors.map(_.exp) ++ methods.map(_.exp))

    case Expr.RunWith(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.NewChannel(exp, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++ visitExp(exp)

    case Expr.GetChannel(exp, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++ visitExp(exp)

    case Expr.PutChannel(exp1, exp2, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++ visitExp(exp1) ++ visitExp(exp2)

    case Expr.Spawn(exp1, exp2, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++ visitExp(exp1) ++ visitExp(exp2)

    case Expr.SelectChannel(selects, optExp, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++
        visitExps(selects.map(_.exp)) ++ visitExps(selects.map(_.chan)) ++ optExp.map(visitExp).getOrElse(Set.empty)

    case Expr.ParYield(frags, exp, _, _, _) =>
      Set(ReachableSym.ChannelUsed) ++ visitExps(frags.map(_.exp)) ++ visitExp(exp)

    case Expr.Lazy(exp, _, _) =>
      visitExp(exp)

    case Expr.Force(exp, _, _, _) =>
      visitExp(exp)

    case Expr.FixpointConstraintSet(cs, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ cs.map(visitConstraint).fold(Set.empty)(_ ++ _)

    case Expr.FixpointLambda(_, exp, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ visitExp(exp)

    case Expr.FixpointMerge(exp1, exp2, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ visitExp(exp1) ++ visitExp(exp2)

    case Expr.FixpointQueryWithProvenance(exps, select, _, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ visitExps(exps) ++ visitHead(select)

    case Expr.FixpointQueryWithSelect(exps, queryExp, selects, from0, where0, _, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++
        visitExps(exps) ++
        visitExp(queryExp) ++
        visitExps(selects) ++
        visitBodies(from0) ++
        visitExps(where0)

    case Expr.FixpointSolveWithProject(exps0, _, _, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ visitExps(exps0)

    case Expr.FixpointInjectInto(exps, _, _, _, _) =>
      Set(ReachableSym.DatalogUsed) ++ visitExps(exps)

    case Expr.Error(m, _, _) =>
      throw InternalCompilerException(s"Unexpected error expression near", m.loc)
  }

  /** Returns the symbols reachable from `exps`. */
  private def visitExps(exps: List[Expr]): Set[ReachableSym] =
    exps.map(visitExp).fold(Set.empty)(_ ++ _)

  /** Returns the symbols reachable from `cs`. */
  private def visitConstraint(cs: Constraint): Set[ReachableSym] =
    visitHead(cs.head) ++ visitBodies(cs.body)

  /** Returns the symbols reachable from `bodies`. */
  private def visitBodies(bodies: List[Predicate.Body]): Set[ReachableSym] =
    bodies.map(visitBody).fold(Set.empty)(_ ++ _)

  /** Returns the symbols reachable from `head`. */
  private def visitHead(head: Predicate.Head): Set[ReachableSym] = head match {
    case Head.Atom(_, _, exps, _, _) => visitExps(exps)
  }

  /** Returns the symbols reachable from `body`. */
  private def visitBody(body: Predicate.Body): Set[ReachableSym] = body match {
    case Body.Atom(_, _, _, _, _, _, _) => Set.empty
    case Body.Functional(_, exp, _) => visitExp(exp)
    case Body.Guard(exp, _) => visitExp(exp)
  }

  /** Reachable symbols (defs, traits, sigs). */
  private sealed trait ReachableSym

  private object ReachableSym {

    case class DefnSym(sym: Symbol.DefnSym) extends ReachableSym

    case class TraitSym(sym: Symbol.TraitSym) extends ReachableSym

    case class SigSym(sym: Symbol.SigSym) extends ReachableSym

    /** Sentinel marking that a Channel-family expression was encountered. */
    case object ChannelUsed extends ReachableSym

    /** Sentinel marking that a Datalog-family expression was encountered. */
    case object DatalogUsed extends ReachableSym

  }

}
