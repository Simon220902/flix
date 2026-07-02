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
import ca.uwaterloo.flix.language.ast.{Kind, Name, RigidityEnv, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.language.phase.typer.{Progress, TypeReduction2}
import ca.uwaterloo.flix.util.InternalCompilerException
import ca.uwaterloo.flix.util.collection.{CofiniteSet, ListMap}

import scala.collection.immutable.SortedSet

/**
  * The single, shared definition of "what a given (possibly non-ground) monomorph type becomes":
  * effect canonicalization, associated-type reduction, and defaulting of unresolved kinds.
  *
  * Both the solver (`ConstraintSolver`, which computes types symbolically, ahead of time) and the
  * specializer (`SolutionSpecialization`, which computes the logically same types concretely, at
  * an actual call site) must agree on this, or their `(sym, type)` defTable keys diverge for the
  * same instantiation. See `notes/plan_canonicalization_unification.md` for the full argument.
  *
  * Lifted from `SolutionSpecialization.scala`'s `StrictSubstitution` (the pipeline's actual source
  * of truth for what canonicalization should produce). `Specialization.scala` (the demand-driven
  * baseline) keeps its own separate copy — out of scope, see that plan doc.
  */
private[monomorph2] object MonomorphCanon {

  /**
    * Builds a lookup map from `(trait, type constructor)` to the instance implementing it.
    * Shared by the solver (sig dispatch, `resolveSig`) and the specializer (`ApplySig`
    * resolution) — pure data reshaping, not part of canonicalization proper, but duplicated
    * the same way across both, so it lives here too. `Specialization.scala` (the demand-driven
    * baseline) keeps its own separate copy — out of scope, see the plan doc.
    */
  def mkInstanceMap(instances: ListMap[Symbol.TraitSym, TypedAst.Instance]): Map[(Symbol.TraitSym, TypeConstructor), TypedAst.Instance] =
    instances.map { case (sym, inst) => ((sym, inst.tpe.typeConstructor.get), inst) }.toMap

  /** Returns the canonical form of the ground effect type `eff`. */
  def canonicalEffect(eff: Type): Type = coSetToType(evalEffect(eff), eff.loc)

  /**
    * Evaluates the ground effect `eff` to a set of effect symbols.
    *
    * N.B.: `eff` must be ground (no free type variables).
    */
  def evalEffect(eff: Type): CofiniteSet[Symbol.EffSym] = eff match {
    case Type.Univ                                                                        => CofiniteSet.universe
    case Type.Pure                                                                        => CofiniteSet.empty
    case Type.Cst(TypeConstructor.Effect(sym, _), _)                                     => CofiniteSet.mkSet(sym)
    case Type.Cst(TypeConstructor.Region(_), _)                                          => CofiniteSet.mkSet(Symbol.IO)
    case Type.Alias(_, _, inner, _)                                                      => evalEffect(inner)
    case Type.Apply(Type.Cst(TypeConstructor.Complement, _), y, _)                       => CofiniteSet.complement(evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Union, _), x, _), y, _)          => CofiniteSet.union(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Intersection, _), x, _), y, _)  => CofiniteSet.intersection(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Difference, _), x, _), y, _)    => CofiniteSet.difference(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SymmetricDiff, _), x, _), y, _) => CofiniteSet.xor(evalEffect(x), evalEffect(y))
    case other => throw InternalCompilerException(s"Unexpected effect $other", other.loc)
  }

  /** Returns the [[Type]] representation of `set` at `loc`. */
  def coSetToType(set: CofiniteSet[Symbol.EffSym], loc: SourceLocation): Type = set match {
    case CofiniteSet.Set(s)   => Type.mkUnion(s.toList.map(sym => Type.Cst(TypeConstructor.Effect(sym, Kind.Eff), loc)), loc)
    case CofiniteSet.Compl(s) => Type.mkComplement(Type.mkUnion(s.toList.map(sym => Type.Cst(TypeConstructor.Effect(sym, Kind.Eff), loc)), loc), loc)
  }

  /** Reduces a ground associated type to its concrete type via the EqualityEnv. */
  def reduceAssocType(assoc: Type.AssocType)(implicit root: TypedAst.Root, flix: Flix): Type = {
    val progress = Progress()
    val (res, cs) = TypeReduction2.reduce(assoc)(RegionScope.Top, RigidityEnv.empty, progress, root.eqEnv, flix)
    if (cs.nonEmpty) throw InternalCompilerException(s"unexpected constraints: $cs", assoc.loc)
    if (progress.query()) res
    else throw InternalCompilerException(s"Could not reduce associated type $assoc", assoc.loc)
  }

  /**
    * Rebuilds `Type.Apply(normalize(tpe1), normalize(tpe2), loc)`, folding ground effect and
    * case-set/record-row/schema-row formulas via the same smart constructors used elsewhere, so
    * the result matches what the specializer's query is built from (e.g. `{Cst} + {}` collapses
    * to `{Cst}`, not a raw `CaseUnion` node; a ground effect formula collapses to its canonical
    * union-of-constants form).
    */
  def normalizeApply(normalize: Type => Type, app: Type.Apply, isGround: Boolean): Type = {
    val Type.Apply(tpe1, tpe2, loc) = app
    val x = normalize(tpe1)
    val y = normalize(tpe2)
    // ponytail: check result's kind, not original's — substitution may change a higher-kinded var's kind
    (x, y) match {
      case _ if isGround && Type.Apply(x, y, loc).kind == Kind.Eff => canonicalEffect(Type.Apply(x, y, loc))
      case (Type.Cst(TypeConstructor.Complement, _), y) => Type.mkComplement(y, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.Union, _), x, _), y) => Type.mkUnion(x, y, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.Intersection, _), x, _), y) => Type.mkIntersection(x, y, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.Difference, _), x, _), y) => Type.mkDifference(x, y, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.SymmetricDiff, _), x, _), y) => Type.mkSymmetricDiff(x, y, loc)
      case (Type.Cst(TypeConstructor.CaseComplement(sym), _), y) => Type.mkCaseComplement(y, sym, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.CaseIntersection(sym), _), x, _), y) => Type.mkCaseIntersection(x, y, sym, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.CaseUnion(sym), _), x, _), y) => Type.mkCaseUnion(x, y, sym, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.RecordRowExtend(label), _), tpe, _), rest) =>
        mkRecordExtendSorted(label, tpe, rest, loc)
      case (Type.Apply(Type.Cst(TypeConstructor.SchemaRowExtend(label), _), tpe, _), rest) =>
        mkSchemaExtendSorted(label, tpe, rest, loc)
      case (x, y) => app.renew(x, y, loc)
    }
  }

  /**
    * Canonicalizes `tpe`: folds ground effect/case-set/row formulas via [[normalizeApply]] and
    * reduces ground associated types via [[reduceAssocType]]. When `isGround` is true, `tpe` is
    * expected to have no free type variables left (used by [[default]] callers after defaulting).
    */
  def simplify(tpe: Type, isGround: Boolean)(implicit root: TypedAst.Root, flix: Flix): Type = tpe match {
    case v@Type.Var(_, _)          => v
    case c@Type.Cst(_, _)          => c
    case app@Type.Apply(_, _, _)   => normalizeApply(simplify(_, isGround), app, isGround)
    case Type.Alias(_, _, t, _)    => simplify(t, isGround)
    case Type.AssocType(symUse, arg0, kind, loc) =>
      val arg = simplify(arg0, isGround)
      simplify(reduceAssocType(Type.AssocType(symUse, arg, kind, loc)), isGround)
    case Type.JvmToType(_, loc)         => throw InternalCompilerException("unexpected JVM type", loc)
    case Type.JvmToEff(_, loc)          => throw InternalCompilerException("unexpected JVM eff", loc)
    case Type.UnresolvedJvmType(_, loc) => throw InternalCompilerException("unexpected JVM type", loc)
  }

  /**
    * Defaults an unresolved (stray) type to its kind's ground default: `Star` (and other
    * value-like kinds) → `AnyType`, `Eff` → `Pure`, `CaseSet` → the empty case set, `SchemaRow` →
    * the empty row. Unconditional — see `notes/plan_canonicalization_unification.md` Part B for
    * why defaulting a trait-constrained `Star` var can only fail safely, not unsoundly.
    */
  def default(tpe0: Type): Type = tpe0.kind match {
    case Kind.Wild          => Type.mkAnyType(tpe0.loc)
    case Kind.WildCaseSet   => Type.mkAnyType(tpe0.loc)
    case Kind.Star          => Type.mkAnyType(tpe0.loc)
    case Kind.Eff           => Type.Pure
    case Kind.Bool          => Type.mkAnyType(tpe0.loc)
    case Kind.RecordRow     => Type.RecordRowEmpty
    case Kind.SchemaRow     => Type.SchemaRowEmpty
    case Kind.Predicate     => Type.mkAnyType(tpe0.loc)
    case Kind.CaseSet(sym)  => Type.Cst(TypeConstructor.CaseSet(SortedSet.empty, sym), tpe0.loc)
    case Kind.Arrow(_, _)   => Type.mkAnyType(tpe0.loc)
    case Kind.Jvm           => throw InternalCompilerException(s"Unexpected type: '$tpe0'.", tpe0.loc)
    case Kind.Error         => throw InternalCompilerException(s"Unexpected type '$tpe0'.", tpe0.loc)
  }

  // ---- Record / schema helpers (used only by normalizeApply) ------------------

  private def mkRecordExtendSorted(label: Name.Label, tpe: Type, rest: Type, loc: SourceLocation): Type = rest match {
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.RecordRowExtend(l), loc1), t, loc2), r, loc3) if l.name < label.name =>
      val newRest = mkRecordExtendSorted(label, tpe, r, loc)
      Type.Apply(Type.Apply(Type.Cst(TypeConstructor.RecordRowExtend(l), loc1), t, loc2), newRest, loc3)
    case Type.Cst(_, _) | Type.Apply(_, _, _) | Type.Var(_, _) =>
      Type.mkRecordRowExtend(label, tpe, rest, loc)
    case Type.Alias(_, _, _, _)         => throw InternalCompilerException(s"Unexpected alias '$rest'", rest.loc)
    case Type.AssocType(_, _, _, _)     => throw InternalCompilerException(s"Unexpected associated type '$rest'", rest.loc)
    case Type.JvmToType(_, _)           => throw InternalCompilerException(s"Unexpected JVM type '$rest'", rest.loc)
    case Type.JvmToEff(_, _)            => throw InternalCompilerException(s"Unexpected JVM eff '$rest'", rest.loc)
    case Type.UnresolvedJvmType(_, _)   => throw InternalCompilerException(s"Unexpected JVM type '$rest'", rest.loc)
  }

  private def mkSchemaExtendSorted(label: Name.Pred, tpe: Type, rest: Type, loc: SourceLocation): Type = rest match {
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SchemaRowExtend(l), loc1), t, loc2), r, loc3) if l.name < label.name =>
      val newRest = mkSchemaExtendSorted(label, tpe, r, loc)
      Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SchemaRowExtend(l), loc1), t, loc2), newRest, loc3)
    case Type.Cst(_, _) | Type.Apply(_, _, _) | Type.Var(_, _) =>
      Type.mkSchemaRowExtend(label, tpe, rest, loc)
    case Type.Alias(_, _, _, _)         => throw InternalCompilerException(s"Unexpected alias '$rest'", rest.loc)
    case Type.AssocType(_, _, _, _)     => throw InternalCompilerException(s"Unexpected associated type '$rest'", rest.loc)
    case Type.JvmToType(_, _)           => throw InternalCompilerException(s"Unexpected JVM type '$rest'", rest.loc)
    case Type.JvmToEff(_, _)            => throw InternalCompilerException(s"Unexpected JVM eff '$rest'", rest.loc)
    case Type.UnresolvedJvmType(_, _)   => throw InternalCompilerException(s"Unexpected JVM type '$rest'", rest.loc)
  }
}
