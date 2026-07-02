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
import ca.uwaterloo.flix.language.ast.TypedAst.{Binder, Expr, Instance, StructField}
import ca.uwaterloo.flix.language.ast.shared.SymUse.{CaseSymUse, DefSymUse, LocalDefSymUse, StructFieldSymUse}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.language.ast.{AtomicOp, Kind, MonoAst, RigidityEnv, SemanticOp, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.dbg.AstPrinter.*
import ca.uwaterloo.flix.language.phase.monomorph.Symbols
import ca.uwaterloo.flix.language.phase.monomorph2.ConstraintSolver.Solution
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.language.phase.unification.Substitution
import ca.uwaterloo.flix.util.collection.{ListOps, MapOps, Nel}
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import scala.collection.mutable

/**
  * Solution-driven specialization: uses the solver solution from Phase 3 to specialize
  * all defs in a single parallel pass, with no demand-driven fallback. Crashes on any
  * call site not covered by the solution ("solver gap"), which identifies missing constraints.
  */
object SolutionSpecialization {

  // ---- Context ----------------------------------------------------------------

  /**
    * Simplified context: only accumulates specialized defs.
    * Unlike Specialization.Context there is no work queue — all specializations are
    * known upfront from the solver solution.
    *
    * `defTable` maps (original sym, instantiated arrow type) → fresh specialized sym.
    * `enumTable`/`structTable` map (original sym, ground type-arg tuple) → fresh specialized
    * sym, mirroring `defTable` — see `lookupCaseSym`/`lookupStructSym` and the `Expr.Tag`/
    * `StructNew`/`StructGet`/`StructPut`/`Pattern.Tag` cases in `specializeExp`/`specializePat`
    * that consult them.
    *
    * package-visible (not `private`): `SolutionLowering.scala` (this pipeline's own fork of
    * `Lowering.scala`) needs it as the type its `ctx` implicit is threaded through.
    */
  private[monomorph2] class Context(
    val defTable: Map[(Symbol.DefnSym, Type), Symbol.DefnSym],
    val allDefs: Map[Symbol.DefnSym, TypedAst.Def],
    val enumTable: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym],
    val structTable: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym]
  ) {
    private val specializedDefs: mutable.Map[Symbol.DefnSym, MonoAst.Def] = mutable.Map.empty

    def addSpecializedDef(sym: Symbol.DefnSym, defn: MonoAst.Def): Unit =
      synchronized { specializedDefs.put(sym, defn) }

    def getSpecializedDefs: Map[Symbol.DefnSym, MonoAst.Def] =
      synchronized { specializedDefs.toMap }
  }

  // ---- lookupSym -------------------------------------------------------------

  /**
    * Returns the sym to use for a call to `sym` instantiated at `it`.
    * - Non-parametric defs: keep original sym.
    * - Parametric defs: must be in defTable (pre-populated from solver solution).
    * - Missing entries: crash with "Solver gap" — this identifies generator/solver gaps.
    *
    * package-visible (not `private`): `SolutionLowering.lookup` calls this directly to resolve
    * lowering-synthesized calls (e.g. channel support functions), instead of
    * `Specialization.specializeDefnSym` — same "Solver gap" failure mode as every other call
    * site in this pipeline, no demand-driven fallback.
    */
  private[monomorph2] def lookupSym(sym: Symbol.DefnSym, it: Type)
                       (implicit ctx: Context, root: TypedAst.Root): Symbol.DefnSym = {
    val defn = ctx.allDefs.getOrElse(sym, throw InternalCompilerException(s"lookupSym: sym not in allDefs: $sym", sym.loc))
    // Check defTable first: polymorphic instance defs and default-sig impls may have empty
    // spec.tparams but still need specialization (via instTparams / traitTparams).
    ctx.defTable.get((sym, it)) match {
      case Some(specializedSym) => specializedSym
      case None if defn.spec.tparams.isEmpty => defn.sym  // truly non-parametric
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no specialization for $sym at type $it. " +
          "Extend the constraint generator to cover this call site.", sym.loc)
    }
  }

  /**
    * Returns the case sym to use for a `Tag`/`Pattern.Tag` whose original case is `caseSym` and
    * whose ground enum type at this expression/pattern site is `groundEnumTpe`.
    * - Non-generic enums (`groundEnumTpe` has no type arguments): keep the original case sym —
    *   there is only one possible instantiation, so nothing was ever entered into `enumTable`
    *   for it (mirrors `lookupSym`'s "truly non-parametric" case for defs).
    * - No type argument is primitive (`MonomorphCanon.isPrimitive`): keep the original case sym
    *   too — this instantiation was never specialized at all (see `enumEntries` in `run`: a
    *   partial specialization needs at least one primitive argument to pin), and this also
    *   covers dead-code `AnyType` defaults (`AnyType` is never primitive) without a separate
    *   check. If *some but not all* arguments are primitive, this is expected to be a hit below
    *   (a partial specialization), not this fallback.
    * - Otherwise: must be in `enumTable` (pre-populated from the solver solution); a miss is a
    *   genuine "Solver gap", same failure mode as `lookupSym`.
    */
  private def lookupCaseSym(caseSym: Symbol.CaseSym, groundEnumTpe: Type)(implicit ctx: Context): Symbol.CaseSym = {
    val argTypes = groundEnumTpe.typeArguments
    ctx.enumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, caseSym.ordinal, caseSym.loc)
      case None if argTypes.isEmpty || !argTypes.exists(MonomorphCanon.isPrimitive) => caseSym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no enum specialization for ${caseSym.enumSym} at $argTypes. " +
          "Extend the constraint generator to cover this call site.", caseSym.loc)
    }
  }

  /**
    * Returns the struct sym to use for a `StructNew`/`StructGet`/`StructPut` whose original
    * struct is `sym` and whose ground struct type at this expression site is `groundStructTpe`.
    * Same "non-generic / no-primitive-argument keeps original, otherwise must be in
    * `structTable`, miss is a Solver gap" shape as `lookupCaseSym`.
    */
  private def lookupStructSym(sym: Symbol.StructSym, groundStructTpe: Type)(implicit ctx: Context): Symbol.StructSym = {
    val argTypes = groundStructTpe.typeArguments
    ctx.structTable.get((sym, argTypes)) match {
      case Some(freshStructSym) => freshStructSym
      case None if argTypes.isEmpty || !argTypes.exists(MonomorphCanon.isPrimitive) => sym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no struct specialization for $sym at $argTypes. " +
          "Extend the constraint generator to cover this call site.", groundStructTpe.loc)
    }
  }

  /**
    * Runs `lookup` (a `lookupCaseSym`/`lookupStructSym` call), falling back to `keep` if it
    * throws — used where a "Solver gap" miss doesn't necessarily mean a real constraint-generator
    * gap (see `rewriteAtomicOp`'s doc comment for why: post-lowering types don't always match the
    * pre-lowering keys `enumTable`/`structTable` were built from).
    */
  private def tolerant[A](lookup: => A, keep: => A): A =
    try lookup catch { case _: InternalCompilerException => keep }

  /**
    * Projects `tuple` to its "specialization signature" for grouping: a primitive argument is
    * kept exactly (two tuples only share a declaration if they agree on every primitive
    * position), a non-primitive argument collapses to a single `AnyType` marker used *only* as a
    * grouping key (`Type.Cst` equality ignores `loc`, so this groups correctly regardless of
    * where each non-primitive type came from) — never used to build an actual field type, see
    * `partialSubst`.
    */
  private def specializationSignature(tuple: List[Type]): List[Type] =
    tuple.map(t => if (MonomorphCanon.isPrimitive(t)) t else Type.mkAnyType(t.loc))

  /**
    * Builds the substitution — and the surviving type parameter list — for one partially
    * specialized declaration from its `signature` (see `specializationSignature`): a primitive
    * position substitutes the declaration's tparam with the pinned concrete type; a non-primitive
    * position substitutes it with a *fresh* type variable instead, kept (in original order) in
    * the returned `survivingTparams` list so the specialized declaration stays genuinely generic
    * in that position — e.g. `Result[Int32, String]`/`Result[Int32, Option[Int32]]` share
    * `Result$N[b] { case Ok(Int32), case Err(b) }`.
    *
    * Deliberately does NOT go through `StrictSubstitution`/`MonomorphCanon.default`: `default`
    * would treat the fresh variable as an unconstrained stray var and default it straight to
    * `AnyType`, silently collapsing this back into "erase to Object" — the design explicitly
    * rejected in favor of this one. Instead this mirrors how `visitEnumCase`/`visitStructField`
    * already treat the *original*, still-polymorphic declaration's field types
    * (`MonomorphCanon.simplify(_, isGround = false)`, at the call sites below): fold structural
    * type formulas without forcing groundness or defaulting anything.
    */
  private def partialSubst(tparams: List[TypedAst.TypeParam], signature: List[Type])
                           (implicit flix: Flix): (Map[Symbol.KindedTypeVarSym, Type], List[TypedAst.TypeParam]) = {
    implicit val scope: RegionScope = RegionScope.Top
    val pairs = tparams.zip(signature).map {
      case (tp, sig) if MonomorphCanon.isPrimitive(sig) => (tp.sym -> sig, None)
      case (tp, _) =>
        val fv = Type.freshVar(tp.sym.kind, tp.loc)
        (tp.sym -> fv, Some(TypedAst.TypeParam(tp.name, fv.sym, tp.loc)))
    }
    (pairs.map(_._1).toMap, pairs.flatMap(_._2))
  }

  // ---- StrictSubstitution (verbatim from Specialization) ----------------------

  /** The effect that all [[TypeConstructor.Region]] are instantiated to. */
  private val RegionInstantiation: TypeConstructor.Effect =
    TypeConstructor.Effect(Symbol.IO, Kind.Eff)

  private object StrictSubstitution {
    val empty: StrictSubstitution = StrictSubstitution(Substitution.empty)

    def mk(s: Substitution)(implicit root: TypedAst.Root, flix: Flix): StrictSubstitution = {
      val m = s.m.map {
        case (sym, tpe) => sym -> MonomorphCanon.simplify(tpe.map(MonomorphCanon.default), isGround = true)
      }
      StrictSubstitution(Substitution(m))
    }
  }

  private case class StrictSubstitution(s: Substitution) {
    def apply(tpe0: Type)(implicit root: TypedAst.Root, flix: Flix): Type = tpe0 match {
      case v@Type.Var(sym, _) => s.m.get(sym) match {
        case None    => MonomorphCanon.default(v)
        case Some(t) => t
      }
      case Type.Cst(TypeConstructor.Region(_), loc) => Type.Cst(RegionInstantiation, loc)
      case cst@Type.Cst(_, _)                       => cst
      case app@Type.Apply(_, _, _)                  => MonomorphCanon.normalizeApply(apply, app, isGround = true)
      case Type.Alias(_, _, t, _)                   => apply(t)
      case Type.AssocType(symUse, arg0, kind, loc) =>
        val arg = apply(arg0)
        val assoc = Type.AssocType(symUse, arg, kind, loc)
        val reducedType = MonomorphCanon.reduceAssocType(assoc)
        MonomorphCanon.simplify(reducedType, isGround = true)
      case Type.JvmToType(_, loc)          => throw InternalCompilerException("unexpected JVM type", loc)
      case Type.JvmToEff(_, loc)           => throw InternalCompilerException("unexpected JVM eff", loc)
      case Type.UnresolvedJvmType(_, loc)  => throw InternalCompilerException("unexpected JVM type", loc)
    }

    def nonStrict: Substitution = s
  }

  // ---- Helpers (verbatim from Specialization) ---------------------------------

  def visitStructField(field: TypedAst.StructField)(implicit root: TypedAst.Root, flix: Flix): TypedAst.StructField =
    field match {
      case TypedAst.StructField(fieldSym, tpe, loc) =>
        TypedAst.StructField(fieldSym, MonomorphCanon.simplify(tpe, isGround = false), loc)
    }

  def visitEnumCase(caze: TypedAst.Case)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Case =
    caze match {
      case TypedAst.Case(sym, tpes, sc, loc) =>
        TypedAst.Case(sym, tpes.map(MonomorphCanon.simplify(_, isGround = false)), sc, loc)
    }

  def visitRestrictableEnumCase(caze: TypedAst.RestrictableCase)(implicit root: TypedAst.Root, flix: Flix): TypedAst.RestrictableCase =
    caze match {
      case TypedAst.RestrictableCase(caseSym0, tpes, sc, loc) =>
        TypedAst.RestrictableCase(caseSym0, tpes.map(MonomorphCanon.simplify(_, isGround = false)), sc, loc)
    }

  private def visitEffectOp(op: TypedAst.Op)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Op =
    op match {
      case TypedAst.Op(sym, TypedAst.Spec(doc, ann, mod, tparams, fparams0, declaredScheme, retTpe, eff, tconstrs, econstrs), loc) =>
        val fparams = fparams0.map {
          case TypedAst.FormalParam(varSym, tpe, src, decreasing, fpLoc) =>
            TypedAst.FormalParam(varSym, StrictSubstitution.empty(tpe), src, decreasing, fpLoc)
        }
        val spec = TypedAst.Spec(doc, ann, mod, tparams, fparams, declaredScheme, StrictSubstitution.empty(retTpe), StrictSubstitution.empty(eff), tconstrs, econstrs)
        TypedAst.Op(sym, spec, loc)
    }

  private def specializeDef(freshSym: Symbol.DefnSym, defn: TypedAst.Def, subst: StrictSubstitution)
                            (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.Def = {
    try {
      val (specializedFparams, env0) = specializeFormalParams(defn.spec.fparams, subst)
      val specializedExp = specializeExp(defn.exp, env0, subst)
      val spec0 = defn.spec
      val declaredScheme = spec0.declaredScheme.copy(base = subst(spec0.declaredScheme.base))
      val spec = TypedAst.Spec(spec0.doc, spec0.ann, spec0.mod, spec0.tparams, specializedFparams,
        declaredScheme, subst(spec0.retTpe), subst(spec0.eff), spec0.tconstrs, spec0.econstrs)
      TypedAst.Def(freshSym, spec, specializedExp, defn.loc)
    } catch {
      case e: InternalCompilerException =>
        throw InternalCompilerException(s"[in ${defn.sym} (subst: $subst)]: ${e.message}", e.loc)
    }
  }

  // ---- specializeExp (verbatim from Specialization except ApplyDef/ApplySig) --

  private def specializeExp(exp0: TypedAst.Expr, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                            (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.Expr = exp0 match {

    case Expr.Var(sym, tpe, loc) =>
      Expr.Var(env0(sym), subst(tpe), loc)

    case Expr.Cst(cst, tpe, loc) =>
      Expr.Cst(cst, subst(tpe), loc)

    case Expr.Hole(sym, scp, tpe, eff, loc) =>
      Expr.Hole(sym, scp, subst(tpe), subst(eff), loc)

    case Expr.HoleWithExp(exp, scp, tpe, eff, loc) =>
      Expr.HoleWithExp(specializeExp(exp, env0, subst), scp, subst(tpe), subst(eff), loc)

    case Expr.OpenAs(symUse, exp, tpe, loc) =>
      Expr.OpenAs(symUse, specializeExp(exp, env0, subst), subst(tpe), loc)

    case Expr.Use(symbol, alias, exp, loc) =>
      Expr.Use(symbol, alias, specializeExp(exp, env0, subst), loc)

    case Expr.Lambda(fparam, exp, tpe, loc) =>
      val (p, env1) = specializeFormalParam(fparam, subst)
      Expr.Lambda(p, specializeExp(exp, env0 ++ env1, subst), subst(tpe), loc)

    case Expr.ApplyClo(exp1, exp2, tpe, eff, pos, loc) =>
      Expr.ApplyClo(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), pos, loc)

    case Expr.ApplyDef(symUse, exps, targs, itpe, tpe, eff, pos, loc) =>
      val it = subst(itpe)
      // ponytail: crash on solver gaps instead of demand-driven fallback
      val newSym = lookupSym(symUse.sym, it)
      val es = exps.map(specializeExp(_, env0, subst))
      Expr.ApplyDef(DefSymUse(newSym, symUse.loc), es, targs, it, subst(tpe), subst(eff), pos, loc)

    case Expr.ApplyLocalDef(symUse, exps, arrowTpe, tpe, eff, pos, loc) =>
      Expr.ApplyLocalDef(LocalDefSymUse(env0(symUse.sym), symUse.loc),
        exps.map(specializeExp(_, env0, subst)), subst(arrowTpe), subst(tpe), subst(eff), pos, loc)

    case Expr.ApplyOp(sym, exps, tpe, eff, pos, loc) =>
      Expr.ApplyOp(sym, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), pos, loc)

    case Expr.ApplySig(symUse, exps, _, targs, itpe, tpe, eff, pos, loc) =>
      val it = subst(itpe)
      val resolvedDef = resolveSigSym(symUse.sym, it)
      val newSym = lookupSym(resolvedDef.sym, it)
      val es = exps.map(specializeExp(_, env0, subst))
      Expr.ApplyDef(DefSymUse(newSym, symUse.loc), es, targs, it, subst(tpe), subst(eff), pos, loc)

    case Expr.Unary(sop, exp, tpe, eff, loc) => sop match {
      case SemanticOp.ReflectOp.ReflectEff =>
        val expTpe = subst(exp.tpe)
        val typeArg = expTpe.typeArguments.headOption.getOrElse(
          throw InternalCompilerException(s"Expected ProxyEff[ef] type, got $expTpe", loc))
        val purityEnumSym = Symbols.Enums.Purity
        val caseName = typeArg match {
          case Type.Cst(TypeConstructor.Pure, _) => "Pure"
          case _                                 => "Impure"
        }
        val caseSym = root.enums(purityEnumSym).cases.values.find(_.sym.name == caseName).get.sym
        Expr.Tag(CaseSymUse(caseSym, loc), Nil, Type.mkEnum(purityEnumSym, Nil, loc), Type.Pure, loc)

      case SemanticOp.ReflectOp.ReflectType =>
        val expTpe = subst(exp.tpe)
        val typeArg = expTpe.typeArguments.headOption.getOrElse(
          throw InternalCompilerException(s"Expected Proxy[t] type, got $expTpe", loc))
        val jvmTypeEnumSym = Symbols.Enums.JvmType
        val caseName = typeArg.baseType match {
          case Type.Cst(TypeConstructor.Bool, _)    => "JvmBool"
          case Type.Cst(TypeConstructor.Char, _)    => "JvmChar"
          case Type.Cst(TypeConstructor.Int8, _)    => "JvmInt8"
          case Type.Cst(TypeConstructor.Int16, _)   => "JvmInt16"
          case Type.Cst(TypeConstructor.Int32, _)   => "JvmInt32"
          case Type.Cst(TypeConstructor.Int64, _)   => "JvmInt64"
          case Type.Cst(TypeConstructor.Float32, _) => "JvmFloat32"
          case Type.Cst(TypeConstructor.Float64, _) => "JvmFloat64"
          case _                                    => "JvmObject"
        }
        val caseSym = root.enums(jvmTypeEnumSym).cases.values.find(_.sym.name == caseName).get.sym
        Expr.Tag(CaseSymUse(caseSym, loc), Nil, Type.mkEnum(jvmTypeEnumSym, Nil, loc), Type.Pure, loc)

      case SemanticOp.ReflectOp.ReflectValue =>
        val e = specializeExp(exp, env0, subst)
        val expTpe = subst(exp.tpe)
        val jvmValueEnumSym = Symbols.Enums.JvmValue
        val resultType = Type.mkEnum(jvmValueEnumSym, Nil, loc)
        val caseName = expTpe.baseType match {
          case Type.Cst(TypeConstructor.Bool, _)    => "JvmBool"
          case Type.Cst(TypeConstructor.Char, _)    => "JvmChar"
          case Type.Cst(TypeConstructor.Int8, _)    => "JvmInt8"
          case Type.Cst(TypeConstructor.Int16, _)   => "JvmInt16"
          case Type.Cst(TypeConstructor.Int32, _)   => "JvmInt32"
          case Type.Cst(TypeConstructor.Int64, _)   => "JvmInt64"
          case Type.Cst(TypeConstructor.Float32, _) => "JvmFloat32"
          case Type.Cst(TypeConstructor.Float64, _) => "JvmFloat64"
          case _                                    => "JvmObject"
        }
        val caseSym = root.enums(jvmValueEnumSym).cases.values.find(_.sym.name == caseName).get.sym
        val tagArg = if (caseName == "JvmObject") {
          val objType = Type.mkNative(classOf[java.lang.Object], loc)
          Expr.UncheckedCast(e, Some(objType), None, objType, Type.Pure, loc)
        } else { e }
        Expr.Tag(CaseSymUse(caseSym, loc), List(tagArg), resultType, subst(eff), loc)

      case _ =>
        Expr.Unary(sop, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)
    }

    case Expr.Binary(sop, exp1, exp2, tpe, eff, loc) =>
      Expr.Binary(sop, specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.Let(bnd, exp1, exp2, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      Expr.Let(Binder(freshSym, subst(bnd.tpe)), specializeExp(exp1, env0, subst), specializeExp(exp2, env1, subst), subst(tpe), subst(eff), loc)

    case Expr.LocalDef(ann, bnd, fparams, exp1, exp2, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      val (fps, env2) = specializeFormalParams(fparams, subst)
      Expr.LocalDef(ann, Binder(freshSym, subst(bnd.tpe)), fps,
        specializeExp(exp1, env1 ++ env2, subst), specializeExp(exp2, env1, subst), subst(tpe), subst(eff), loc)

    case Expr.Region(bnd, regionVar, exp, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      Expr.Region(Binder(freshSym, subst(bnd.tpe)), regionVar, specializeExp(exp, env1, subst), subst(tpe), subst(eff), loc)

    case Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) =>
      Expr.IfThenElse(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), specializeExp(exp3, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.Stm(exps, exp, tpe, eff, loc) =>
      Expr.Stm(exps.map(specializeExp(_, env0, subst)), specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.Discard(exp, eff, loc) =>
      Expr.Discard(specializeExp(exp, env0, subst), subst(eff), loc)

    case Expr.Match(exp, rules, tpe, eff, loc0) =>
      val rs = rules.map {
        case TypedAst.MatchRule(pat, guard, body, loc) =>
          val (p, env1) = specializePat(pat, Map(), subst)
          val extendedEnv = env0 ++ env1
          TypedAst.MatchRule(p, guard.map(specializeExp(_, extendedEnv, subst)), specializeExp(body, extendedEnv, subst), loc)
      }
      Expr.Match(specializeExp(exp, env0, subst), rs, subst(tpe), subst(eff), loc0)

    case Expr.ExtMatch(exp, rules, tpe, eff, loc) =>
      val rs = rules.map {
        case TypedAst.ExtMatchRule(pat, exp1, loc1) =>
          val (p, env1) = specializeExtPat(pat, subst)
          TypedAst.ExtMatchRule(p, specializeExp(exp1, env0 ++ env1, subst), loc1)
      }
      Expr.ExtMatch(specializeExp(exp, env0, subst), rs, subst(tpe), subst(eff), loc)

    case Expr.RestrictableChoose(star, exp, rules, tpe, eff, loc) =>
      Expr.RestrictableChoose(star, specializeExp(exp, env0, subst), rules.map(specializeRestrictableChooseRule(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.Tag(symUse, exps, tpe, eff, loc) =>
      // The tag's own result type IS the enum's ground type at this construction site (mirrors
      // Eraser.specializedCaseSym, which uses the ApplyAtomic's own `t` for the same reason).
      val t = subst(tpe)
      val newSym = lookupCaseSym(symUse.sym, t)
      Expr.Tag(CaseSymUse(newSym, symUse.loc), exps.map(specializeExp(_, env0, subst)), t, subst(eff), loc)

    case Expr.RestrictableTag(symUse, exps, tpe, eff, loc) =>
      Expr.RestrictableTag(symUse, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.ExtTag(label, exps, tpe, eff, loc) =>
      Expr.ExtTag(label, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.Tuple(exps, tpe, eff, loc) =>
      Expr.Tuple(exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.RecordSelect(exp, label, tpe, eff, loc) =>
      Expr.RecordSelect(specializeExp(exp, env0, subst), label, subst(tpe), subst(eff), loc)

    case Expr.RecordExtend(label, exp1, exp2, tpe, eff, loc) =>
      Expr.RecordExtend(label, specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.RecordRestrict(label, exp, tpe, eff, loc) =>
      Expr.RecordRestrict(label, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.ArrayLit(exps, exp, tpe, eff, loc) =>
      Expr.ArrayLit(exps.map(specializeExp(_, env0, subst)), specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.ArrayNew(exp1, exp2, exp3, tpe, eff, loc) =>
      Expr.ArrayNew(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), specializeExp(exp3, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.ArrayLoad(exp1, exp2, tpe, eff, loc) =>
      Expr.ArrayLoad(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.ArrayLength(exp, eff, loc) =>
      Expr.ArrayLength(specializeExp(exp, env0, subst), subst(eff), loc)

    case Expr.ArrayStore(exp1, exp2, exp3, eff, loc) =>
      Expr.ArrayStore(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), specializeExp(exp3, env0, subst), subst(eff), loc)

    case Expr.StructNew(sym, fields0, region0, tpe, eff, loc) =>
      // The StructNew's own result type IS the struct's ground type at this construction site.
      val t = subst(tpe)
      val newStructSym = lookupStructSym(sym, t)
      val fields = fields0.map { case (symUse, v) =>
        val newFieldSym = new Symbol.StructFieldSym(newStructSym, symUse.sym.name, symUse.loc)
        (StructFieldSymUse(newFieldSym, symUse.loc), specializeExp(v, env0, subst))
      }
      Expr.StructNew(newStructSym, fields, region0.map(specializeExp(_, env0, subst)), t, subst(eff), loc)

    case Expr.StructGet(exp, symUse, tpe, eff, loc) =>
      // Unlike Tag/StructNew (whose own result type IS the enum/struct type), StructGet's own
      // `tpe` is the FIELD's type — the struct being accessed is `exp`'s type instead.
      val e = specializeExp(exp, env0, subst)
      val newStructSym = lookupStructSym(symUse.sym.structSym, subst(exp.tpe))
      val newFieldSym = new Symbol.StructFieldSym(newStructSym, symUse.sym.name, symUse.loc)
      Expr.StructGet(e, StructFieldSymUse(newFieldSym, symUse.loc), subst(tpe), subst(eff), loc)

    case Expr.StructPut(exp1, symUse, exp2, tpe, eff, loc) =>
      val e1 = specializeExp(exp1, env0, subst)
      val newStructSym = lookupStructSym(symUse.sym.structSym, subst(exp1.tpe))
      val newFieldSym = new Symbol.StructFieldSym(newStructSym, symUse.sym.name, symUse.loc)
      Expr.StructPut(e1, StructFieldSymUse(newFieldSym, symUse.loc), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.VectorLit(exps, tpe, eff, loc) =>
      Expr.VectorLit(exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.VectorLoad(exp1, exp2, tpe, eff, loc) =>
      Expr.VectorLoad(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.VectorLength(exp, loc) =>
      Expr.VectorLength(specializeExp(exp, env0, subst), loc)

    case Expr.Ascribe(exp, expectedType, expectedEff, tpe, eff, loc) =>
      Expr.Ascribe(specializeExp(exp, env0, subst), expectedType.map(subst.apply), expectedEff.map(subst.apply), subst(tpe), subst(eff), loc)

    case Expr.InstanceOf(exp, clazz, loc) =>
      Expr.InstanceOf(specializeExp(exp, env0, subst), clazz, loc)

    case Expr.UncheckedCast(exp, declaredType, declaredEff, tpe, eff, loc) =>
      Expr.UncheckedCast(specializeExp(exp, env0, subst), declaredType.map(subst.apply), declaredEff.map(subst.apply), subst(tpe), subst(eff), loc)

    case Expr.CheckedCast(cast, exp, tpe, eff, loc) =>
      Expr.CheckedCast(cast, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.Unsafe(exp, runEff, asEff0, tpe, eff, loc) =>
      Expr.Unsafe(specializeExp(exp, env0, subst), subst(runEff), asEff0.map(subst.apply), subst(tpe), subst(eff), loc)

    case Expr.TryCatch(exp, rules, tpe, eff, loc0) =>
      val rs = rules.map {
        case TypedAst.CatchRule(bnd, clazz, body, loc) =>
          val freshSym = Symbol.freshVarSym(bnd.sym)
          val env1 = env0 + (bnd.sym -> freshSym)
          TypedAst.CatchRule(Binder(freshSym, subst(bnd.tpe)), clazz, specializeExp(body, env1, subst), loc)
      }
      Expr.TryCatch(specializeExp(exp, env0, subst), rs, subst(tpe), subst(eff), loc0)

    case Expr.Throw(exp, tpe, eff, loc) =>
      Expr.Throw(specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.Handler(symUse0, rules0, bodyTpe, bodyEff, handledEff, tpe, loc0) =>
      val rules = rules0.map {
        case TypedAst.HandlerRule(symUse, fparams0, exp, loc) =>
          val (fparams, env1) = specializeFormalParams(fparams0, subst)
          TypedAst.HandlerRule(symUse, fparams, specializeExp(exp, env0 ++ env1, subst), loc)
      }
      Expr.Handler(symUse0, rules, subst(bodyTpe), subst(bodyEff), subst(handledEff), subst(tpe), loc0)

    case Expr.RunWith(exp1, exp2, tpe, eff, loc) =>
      Expr.RunWith(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.InvokeConstructor(constructor, exps, tpe, eff, loc) =>
      Expr.InvokeConstructor(constructor, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.InvokeSuperConstructor(constructor, exps, tpe, eff, loc) =>
      Expr.InvokeSuperConstructor(constructor, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.InvokeMethod(method, exp, exps, tpe, eff, loc) =>
      Expr.InvokeMethod(method, specializeExp(exp, env0, subst), exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.InvokeSuperMethod(method, exps, tpe, eff, loc) =>
      Expr.InvokeSuperMethod(method, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.InvokeStaticMethod(method, exps, tpe, eff, loc) =>
      Expr.InvokeStaticMethod(method, exps.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc)

    case Expr.GetField(field, exp, tpe, eff, loc) =>
      Expr.GetField(field, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.PutField(field, exp1, exp2, tpe, eff, loc) =>
      Expr.PutField(field, specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.GetStaticField(field, tpe, eff, loc) =>
      Expr.GetStaticField(field, subst(tpe), subst(eff), loc)

    case Expr.PutStaticField(field, exp, tpe, eff, loc) =>
      Expr.PutStaticField(field, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.NewObject(sym, clazz, tpe, eff, constructors0, methods0, loc) =>
      Expr.NewObject(sym, clazz, subst(tpe), subst(eff),
        constructors0.map(specializeJvmConstructor(_, env0, subst)),
        methods0.map(specializeJvmMethod(_, env0, subst)), loc)

    case Expr.NewChannel(innerExp, tpe, eff, loc) =>
      Expr.NewChannel(specializeExp(innerExp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.GetChannel(innerExp, tpe, eff, loc) =>
      Expr.GetChannel(specializeExp(innerExp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.PutChannel(innerExp1, innerExp2, tpe, eff, loc) =>
      Expr.PutChannel(specializeExp(innerExp1, env0, subst), specializeExp(innerExp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.SelectChannel(rules0, default0, tpe, eff, loc0) =>
      val rules = rules0.map {
        case TypedAst.SelectChannelRule(bnd, chan0, exp, loc) =>
          val freshSym = Symbol.freshVarSym(bnd.sym)
          val env1 = env0 + (bnd.sym -> freshSym)
          TypedAst.SelectChannelRule(Binder(freshSym, subst(bnd.tpe)), specializeExp(chan0, env1, subst), specializeExp(exp, env1, subst), loc)
      }
      Expr.SelectChannel(rules, default0.map(specializeExp(_, env0, subst)), subst(tpe), subst(eff), loc0)

    case Expr.Spawn(exp1, exp2, tpe, eff, loc) =>
      Expr.Spawn(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.ParYield(frags, exp, tpe, eff, loc) =>
      var curEnv = env0
      val fs = frags.map {
        case TypedAst.ParYieldFragment(pat, fragExp, fragLoc) =>
          val (p, env1) = specializePat(pat, Map(), subst)
          curEnv ++= env1
          TypedAst.ParYieldFragment(p, specializeExp(fragExp, curEnv, subst), fragLoc)
      }
      Expr.ParYield(fs, specializeExp(exp, curEnv, subst), subst(tpe), subst(eff), loc)

    case Expr.Lazy(exp, tpe, loc) =>
      Expr.Lazy(specializeExp(exp, env0, subst), subst(tpe), loc)

    case Expr.Force(exp, tpe, eff, loc) =>
      Expr.Force(specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.FixpointConstraintSet(cs0, tpe, loc) =>
      Expr.FixpointConstraintSet(cs0.map(specializeConstraint(_, env0, subst)), subst(tpe), loc)

    case Expr.FixpointLambda(pparams0, exp, tpe, eff, loc) =>
      val pparams = pparams0.map {
        case TypedAst.PredicateParam(pred, tpe0, loc0) => TypedAst.PredicateParam(pred, subst(tpe0), loc0)
      }
      Expr.FixpointLambda(pparams, specializeExp(exp, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.FixpointMerge(exp1, exp2, tpe, eff, loc) =>
      Expr.FixpointMerge(specializeExp(exp1, env0, subst), specializeExp(exp2, env0, subst), subst(tpe), subst(eff), loc)

    case Expr.FixpointQueryWithProvenance(exps0, select0, withh, tpe, eff, loc) =>
      Expr.FixpointQueryWithProvenance(exps0.map(specializeExp(_, env0, subst)), specializeHeadPred(select0, env0, subst), withh, subst(tpe), subst(eff), loc)

    case Expr.FixpointQueryWithSelect(exps0, queryExp0, selects0, from0, where0, pred, tpe, eff, loc) =>
      Expr.FixpointQueryWithSelect(exps0.map(specializeExp(_, env0, subst)), specializeExp(queryExp0, env0, subst), selects0, from0, where0, pred, subst(tpe), subst(eff), loc)

    case Expr.FixpointSolveWithProject(exps0, optPreds, mode, tpe, eff, loc) =>
      Expr.FixpointSolveWithProject(exps0.map(specializeExp(_, env0, subst)), optPreds, mode, subst(tpe), subst(eff), loc)

    case Expr.FixpointInjectInto(exps0, predsAndArities, tpe, eff, loc) =>
      Expr.FixpointInjectInto(exps0.map(specializeExp(_, env0, subst)), predsAndArities, subst(tpe), subst(eff), loc)

    case Expr.Error(m, _, _) =>
      throw InternalCompilerException(s"Unexpected error expression near", m.loc)
  }

  // ---- specializeExp sub-helpers (verbatim from Specialization) ---------------

  private def specializeHeadPred(p: TypedAst.Predicate.Head, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                 (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.Predicate.Head = p match {
    case TypedAst.Predicate.Head.Atom(pred, den, terms, tpe, loc) =>
      TypedAst.Predicate.Head.Atom(pred, den, terms.map(specializeExp(_, env0, subst)), subst(tpe), loc)
  }

  private def specializeBodyPred(b0: TypedAst.Predicate.Body, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                 (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): (TypedAst.Predicate.Body, Map[Symbol.VarSym, Symbol.VarSym]) = b0 match {
    case TypedAst.Predicate.Body.Atom(pred0, den, polarity, fixity, terms0, tpe, loc) =>
      val (terms, env) = specializePats(terms0, env0, subst)
      (TypedAst.Predicate.Body.Atom(pred0, den, polarity, fixity, terms, subst(tpe), loc), env)
    case TypedAst.Predicate.Body.Functional(outSyms0, exp, loc) =>
      val outSyms = outSyms0.map(bnd => Binder(env0(bnd.sym), subst(bnd.tpe)))
      (TypedAst.Predicate.Body.Functional(outSyms, specializeExp(exp, env0, subst), loc), env0)
    case TypedAst.Predicate.Body.Guard(exp, loc) =>
      (TypedAst.Predicate.Body.Guard(specializeExp(exp, env0, subst), loc), env0)
  }

  private def specializePats(ps: List[TypedAst.Pattern], env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                             (implicit ctx: Context, root: TypedAst.Root, flix: Flix): (List[TypedAst.Pattern], Map[Symbol.VarSym, Symbol.VarSym]) =
    ps.foldRight((Nil: List[TypedAst.Pattern], env0)) {
      case (pat0, (res, env1)) =>
        val (pat, env) = specializePat(pat0, env1, subst)
        (pat :: res, env)
    }

  private def specializeBodies(bodies: List[TypedAst.Predicate.Body], env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                               (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): (List[TypedAst.Predicate.Body], Map[Symbol.VarSym, Symbol.VarSym]) =
    bodies.foldRight((Nil: List[TypedAst.Predicate.Body], env0)) {
      case (body, (res, env1)) =>
        val (pat, env) = specializeBodyPred(body, env1, subst)
        (pat :: res, env)
    }

  private def specializeConstraint(c0: TypedAst.Constraint, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                   (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.Constraint = c0 match {
    case TypedAst.Constraint(cparams0, head0, body0, loc0) =>
      val env = cparams0.foldLeft(env0) {
        case (env1, TypedAst.ConstraintParam(bnd, _, _)) =>
          if (env1.contains(bnd.sym)) env1
          else { val freshSym = Symbol.freshVarSym(bnd.sym); env1 + (bnd.sym -> freshSym) }
      }
      val cparams = cparams0.map {
        case TypedAst.ConstraintParam(bnd, tpe, loc) =>
          TypedAst.ConstraintParam(Binder(env(bnd.sym), subst(bnd.tpe)), subst(tpe), loc)
      }
      val (body, env2) = specializeBodies(body0, env, subst)
      TypedAst.Constraint(cparams, specializeHeadPred(head0, env2, subst), body, loc0)
  }

  private def specializeRestrictableChooseRule(rule0: TypedAst.RestrictableChooseRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                               (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.RestrictableChooseRule = rule0 match {
    case TypedAst.RestrictableChooseRule(pat, exp) =>
      pat match {
        case TypedAst.RestrictableChoosePattern.Tag(symUse, pat0, tpe, loc) =>
          val env = pat0.foldLeft(env0) {
            case (env1, TypedAst.RestrictableChoosePattern.Var(bnd, _, _)) =>
              env1 + (bnd.sym -> Symbol.freshVarSym(bnd.sym))
            case (env1, TypedAst.RestrictableChoosePattern.Wild(_, _)) => env1
            case (_, TypedAst.RestrictableChoosePattern.Error(_, errLoc)) => throw InternalCompilerException("unexpected restrictable choose variable", errLoc)
          }
          val pats = pat0.map {
            case TypedAst.RestrictableChoosePattern.Var(bnd, varTpe, varLoc) =>
              TypedAst.RestrictableChoosePattern.Var(Binder(env(bnd.sym), subst(bnd.tpe)), subst(varTpe), varLoc)
            case TypedAst.RestrictableChoosePattern.Wild(wildTpe, wildLoc) =>
              TypedAst.RestrictableChoosePattern.Wild(subst(wildTpe), wildLoc)
            case TypedAst.RestrictableChoosePattern.Error(_, errLoc) => throw InternalCompilerException("unexpected restrictable choose variable", errLoc)
          }
          TypedAst.RestrictableChooseRule(TypedAst.RestrictableChoosePattern.Tag(symUse, pats, subst(tpe), loc), specializeExp(exp, env, subst))
        case TypedAst.RestrictableChoosePattern.Error(_, loc) => throw InternalCompilerException("unexpected error restrictable choose pattern", loc)
      }
  }

  private def specializePat(p0: TypedAst.Pattern, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                            (implicit ctx: Context, root: TypedAst.Root, flix: Flix): (TypedAst.Pattern, Map[Symbol.VarSym, Symbol.VarSym]) = p0 match {
    case TypedAst.Pattern.Wild(tpe, loc) => (TypedAst.Pattern.Wild(subst(tpe), loc), env0)

    case TypedAst.Pattern.Var(bnd, tpe, loc) =>
      val env = if (env0.contains(bnd.sym)) env0 else env0 + (bnd.sym -> Symbol.freshVarSym(bnd.sym))
      (TypedAst.Pattern.Var(Binder(env(bnd.sym), subst(bnd.tpe)), subst(tpe), loc), env)

    case TypedAst.Pattern.Cst(cst, tpe, loc) => (TypedAst.Pattern.Cst(cst, subst(tpe), loc), env0)

    case TypedAst.Pattern.Tag(symUse, pats, tpe, loc) =>
      val (ps, env) = specializePats(pats, env0, subst)
      // The pattern's own type IS the scrutinee's enum type (mirrors Eraser.specializedCaseSym,
      // which uses the scrutinee's `e.tpe` for the same reason).
      val t = subst(tpe)
      val newSym = lookupCaseSym(symUse.sym, t)
      (TypedAst.Pattern.Tag(CaseSymUse(newSym, symUse.loc), ps, t, loc), env)

    case TypedAst.Pattern.Tuple(elms, tpe, loc) =>
      val (ps, env) = specializePats(elms.toList, env0, subst)
      (TypedAst.Pattern.Tuple(Nel(ps.head, ps.tail), subst(tpe), loc), env)

    case TypedAst.Pattern.Record(pats, pat, tpe, loc) =>
      val (ps, envs) = pats.map {
        case TypedAst.Pattern.Record.RecordLabelPattern(label, pat1, tpe1, loc1) =>
          val (p1, env1) = specializePat(pat1, env0, subst)
          (TypedAst.Pattern.Record.RecordLabelPattern(label, p1, subst(tpe1), loc1), env1)
      }.unzip
      val (p, env1) = specializePat(pat, env0, subst)
      (TypedAst.Pattern.Record(ps, p, subst(tpe), loc), combineEnvs(env1 :: envs))

    case TypedAst.Pattern.Error(_, loc) => throw InternalCompilerException(s"Unexpected pattern: '$p0'.", loc)
  }

  private def specializeExtPat(pat0: TypedAst.ExtPattern, subst: StrictSubstitution)
                               (implicit root: TypedAst.Root, flix: Flix): (TypedAst.ExtPattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case TypedAst.ExtPattern.Default(loc) => (TypedAst.ExtPattern.Default(loc), Map.empty)
    case TypedAst.ExtPattern.Tag(label, pats, loc) =>
      val (ps, symMaps) = pats.map(specializeExtTagPat(_, subst)).unzip
      (TypedAst.ExtPattern.Tag(label, ps, loc), symMaps.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _))
    case TypedAst.ExtPattern.Error(loc) => throw InternalCompilerException("unexpected error ext pattern", loc)
  }

  private def specializeExtTagPat(pat0: TypedAst.ExtTagPattern, subst: StrictSubstitution)
                                  (implicit root: TypedAst.Root, flix: Flix): (TypedAst.ExtTagPattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case TypedAst.ExtTagPattern.Wild(tpe, loc)     => (TypedAst.ExtTagPattern.Wild(subst(tpe), loc), Map.empty)
    case TypedAst.ExtTagPattern.Var(bnd, tpe, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      (TypedAst.ExtTagPattern.Var(Binder(freshSym, subst(bnd.tpe)), subst(tpe), loc), Map(bnd.sym -> freshSym))
    case TypedAst.ExtTagPattern.Unit(tpe, loc)     => (TypedAst.ExtTagPattern.Unit(subst(tpe), loc), Map.empty)
    case TypedAst.ExtTagPattern.Error(_, loc)      => throw InternalCompilerException("unexpected error ext pattern", loc)
  }

  private def specializeJvmConstructor(constructor: TypedAst.JvmConstructor, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                       (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.JvmConstructor = constructor match {
    case TypedAst.JvmConstructor(exp0, tpe, eff, loc) =>
      TypedAst.JvmConstructor(specializeExp(exp0, env0, subst), subst(tpe), subst(eff), loc)
  }

  private def specializeJvmMethod(method: TypedAst.JvmMethod, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)
                                  (implicit ctx: Context, instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.JvmMethod = method match {
    case TypedAst.JvmMethod(ann, ident, fparams0, exp0, tpe, eff, loc) =>
      val (fparams, env1) = specializeFormalParams(fparams0, subst)
      TypedAst.JvmMethod(ann, ident, fparams, specializeExp(exp0, env0 ++ env1, subst), subst(tpe), subst(eff), loc)
  }

  private def resolveSigSym(sym: Symbol.SigSym, tpe: Type)
                            (implicit instances: Map[(Symbol.TraitSym, TypeConstructor), Instance], root: TypedAst.Root, flix: Flix): TypedAst.Def = {
    val sig = root.sigs(sym)
    val trt = root.traits(sym.trt)
    val subst = ConstraintSolver2.fullyUnify(sig.spec.declaredScheme.base, tpe, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix).get
    val traitType = subst.m(trt.tparam.sym)
    val tyCon = traitType.typeConstructor.get
    val instance = instances((sym.trt, tyCon))
    val defns = instance.defs.filter(_.sym.text == sig.sym.name)
    (sig.exp, defns) match {
      case (_, defn :: Nil) => defn
      case (Some(impl), Nil) =>
        val ns = sig.sym.trt.namespace :+ sig.sym.trt.name
        val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
        TypedAst.Def(defnSym, sig.spec, impl, sig.loc)
      case (_, _ :: _ :: _) => throw InternalCompilerException(s"Expected at most one matching definition for '$sym', but found ${defns.size} signatures.", sym.loc)
      case (None, Nil)       => throw InternalCompilerException(s"No default or matching definition found for '$sym'.", sym.loc)
    }
  }

  private def combineEnvs(envs: Iterable[Map[Symbol.VarSym, Symbol.VarSym]]): Map[Symbol.VarSym, Symbol.VarSym] =
    envs.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _)

  private def specializeFormalParams(fparams0: List[TypedAst.FormalParam], subst0: StrictSubstitution)
                                     (implicit root: TypedAst.Root, flix: Flix): (List[TypedAst.FormalParam], Map[Symbol.VarSym, Symbol.VarSym]) = {
    val (params, envs) = fparams0.map(specializeFormalParam(_, subst0)).unzip
    (params, combineEnvs(envs))
  }

  private def specializeFormalParam(fparam0: TypedAst.FormalParam, subst0: StrictSubstitution)
                                    (implicit root: TypedAst.Root, flix: Flix): (TypedAst.FormalParam, Map[Symbol.VarSym, Symbol.VarSym]) = {
    val TypedAst.FormalParam(bnd, tpe, src, decreasing, loc) = fparam0
    val freshSym = Symbol.freshVarSym(bnd.sym)
    (TypedAst.FormalParam(Binder(freshSym, subst0(bnd.tpe)), subst0(tpe), src, decreasing, loc), Map(bnd.sym -> freshSym))
  }

  // ---- Type normalization helpers (verbatim from Specialization) --------------

  private def infallibleUnify(tpe1: Type, tpe2: Type, sym: Symbol.DefnSym)(implicit root: TypedAst.Root, flix: Flix): StrictSubstitution =
    ConstraintSolver2.fullyUnify(tpe1, tpe2, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix) match {
      case Some(subst) => StrictSubstitution.mk(subst)
      case None        => throw InternalCompilerException(s"Unable to unify: '$tpe1' and '$tpe2'.\nIn '$sym'", tpe1.loc)
    }

  // ---- Enum/struct type rewriting (post-lowering) -----------------------------
  //
  // `lookupCaseSym`/`lookupStructSym` (used inside `specializeExp`/`specializePat`, before
  // lowering) already rewrite the *symbol* on Tag/Is/Untag/StructNew/StructGet/StructPut to the
  // fresh specialized enum/struct sym. That alone is not enough: every `Type` value elsewhere in
  // the specialized tree (a `Var`'s type, a `Match`'s scrutinee type, a def's own `functionType`/
  // `retTpe`, ...) still refers to the *original* enum/struct sym with its *concrete, ground*
  // type arguments (e.g. `Enum(List, [Int32])`), since `StrictSubstitution.apply` was never
  // taught about the fresh syms — it just substitutes+canonicalizes, exactly as it always has for
  // defs (which have no equivalent "symbol vs. type" consistency requirement). A downstream
  // consistency check (`main/test/.../verifier/TypeVerifier.scala`, run by `RunVerifiers`/
  // `FlixSuite`) asserts that a `Tag`/`Is`/`Untag`'s case-sym's `enumSym` matches the enum sym
  // embedded in the surrounding type — confirmed directly from its source (the exact "Mismatched
  // shape: expected = 'X$Y', found = Enum(X, args)" message) — so once the symbol is specialized,
  // the type has to be too, everywhere it appears, not just at the Tag/StructNew site itself.
  //
  // This is a full post-pass over each already-specialized-and-lowered `MonoAst.Def`, rewriting
  // every `Type` field via `rewriteEnumStructType`, structurally, wherever it occurs — simplest
  // correct fix, and lower-risk than trying to thread this through every `subst(tpe)` call inside
  // `specializeExp` (of which there are around a hundred): those still produce "raw" types keyed
  // by original sym + concrete args, which is exactly what `lookupCaseSym`/`lookupStructSym`
  // themselves need to extract `argTypes` from in the first place (rewriting the type *before* that
  // lookup would make the lookup key already-rewritten and self-defeating).

  /**
    * Structurally rewrites `tpe`: any `Enum(sym, args)`/`Struct(sym, args)` sub-type whose
    * `(sym, args)` pair is a key in `ctx.enumTable`/`structTable` becomes `Enum(freshSym, Nil)`/
    * `Struct(freshSym, Nil)` (fully specialized, no more type arguments); anything else is left
    * alone except for recursing into its own sub-parts (which may themselves need rewriting,
    * e.g. `List[Option[Int32]]` needs both `List` and `Option` rewritten if both were specialized).
    */
  private def rewriteEnumStructType(tpe: Type)(implicit ctx: Context): Type = tpe match {
    case Type.Apply(_, _, loc) =>
      val head = rewriteTypeAppHead(tpe)
      val args = rewriteTypeAppArgs(tpe)
      head match {
        // Partial specialization (see `partialSubst`): the specialized declaration only kept the
        // non-primitive positions as real type arguments, in original order — the primitive ones
        // were pinned into the declaration itself, so they're dropped here too, not passed as Nil.
        case Type.Cst(TypeConstructor.Enum(sym, _), _) if ctx.enumTable.contains((sym, args)) =>
          val survivingArgs = args.filterNot(MonomorphCanon.isPrimitive).map(rewriteEnumStructType)
          Type.mkEnum(ctx.enumTable((sym, args)), survivingArgs, loc)
        case Type.Cst(TypeConstructor.Struct(sym, _), _) if ctx.structTable.contains((sym, args)) =>
          val survivingArgs = args.filterNot(MonomorphCanon.isPrimitive).map(rewriteEnumStructType)
          Type.mkStruct(ctx.structTable((sym, args)), survivingArgs, loc)
        case _ =>
          args.foldLeft(rewriteEnumStructType(head)) { case (acc, arg) => Type.Apply(acc, rewriteEnumStructType(arg), loc) }
      }
    case Type.Alias(sym, args, inner, loc) =>
      Type.Alias(sym, args.map(rewriteEnumStructType), rewriteEnumStructType(inner), loc)
    case _ => tpe // Var, Cst (incl. already-nullary Enum/Struct), AssocType, etc. — nothing to rewrite.
  }

  private def rewriteTypeAppHead(tpe: Type): Type = tpe match {
    case Type.Apply(t1, _, _) => rewriteTypeAppHead(t1)
    case t => t
  }

  private def rewriteTypeAppArgs(tpe: Type): List[Type] = tpe match {
    case Type.Apply(t1, t2, _) => rewriteTypeAppArgs(t1) :+ t2
    case _ => Nil
  }

  private def rewriteDef(defn: MonoAst.Def)(implicit ctx: Context): MonoAst.Def =
    MonoAst.Def(defn.sym, rewriteSpec(defn.spec), rewriteExpr(defn.exp), defn.loc)

  private def rewriteSpec(spec: MonoAst.Spec)(implicit ctx: Context): MonoAst.Spec =
    spec.copy(
      fparams = spec.fparams.map(rewriteFormalParam),
      functionType = rewriteEnumStructType(spec.functionType),
      retTpe = rewriteEnumStructType(spec.retTpe),
      eff = rewriteEnumStructType(spec.eff)
    )

  private def rewriteFormalParam(fp: MonoAst.FormalParam)(implicit ctx: Context): MonoAst.FormalParam =
    fp.copy(tpe = rewriteEnumStructType(fp.tpe))

  /**
    * `Tag`/`StructNew`/`StructGet`/`StructPut` sites built directly by `specializeExp` (from
    * source `Expr.Tag`/`StructNew`/etc.) already have their symbol rewritten by
    * `lookupCaseSym`/`lookupStructSym` before lowering. But `SolutionLowering.scala`'s Datalog
    * desugaring (`mkTag`, struct lowering for `Fixpoint3.Ast.*`) constructs `AtomicOp.Tag`/
    * `StructNew`/etc. directly as already-lowered `MonoAst`, entirely bypassing `specializeExp` —
    * those symbols are never touched by the TypedAst-level rewrite. `rewriteEnumStructType` (the
    * type-level post-pass) rewrites the *type* on these nodes regardless of origin (it's a
    * structural walk, origin-agnostic), which on its own left such nodes with a rewritten type
    * but an unrewritten symbol — the reverse of the original type/symbol mismatch, caught by
    * `TypeVerifier` the same way. Rewriting the symbol here too, using the exact same
    * `lookupCaseSym`/`lookupStructSym` used at the TypedAst level, closes that gap and is a no-op
    * (idempotent) on nodes that were already correctly rewritten upstream.
    *
    * The lookup can also genuinely miss here for a reason that has nothing to do with a real
    * "Solver gap": `enumTable`/`structTable` are keyed by *pre-lowering* TypedAst ground types,
    * but this runs on *post-lowering* MonoAst types — and `SolutionLowering`'s `lowerType`
    * transforms some type components in ways the key was never built to match (e.g. a struct's
    * region type parameter becomes an `IO` effect after lowering). When that happens, `resultTpe`
    * itself is left partially unrewritten by `rewriteEnumStructType` (silently — it has no "miss"
    * case, it just doesn't rewrite that part), so the symbol should likewise stay exactly as it
    * already was: if this node's symbol was already correctly specialized upstream (the common
    * case, since most of these nodes go through `specializeExp` first), leaving it alone is
    * correct; if it wasn't, leaving it alone keeps it consistent with the equally-unrewritten
    * type, rather than guessing and risking a new mismatch. Escalating to "Solver gap" here would
    * conflate this representation mismatch with an actual constraint-generator gap.
    */
  private def rewriteAtomicOp(op: AtomicOp, exps: List[MonoAst.Expr], rawResultTpe: Type)(implicit ctx: Context): AtomicOp = {
    // NB: `lookupCaseSym`/`lookupStructSym` need the *raw* (pre-rewrite) ground type to extract
    // the original concrete type arguments as a lookup key — passing the already-rewritten type
    // (whose args are `Nil` once specialized) makes every lookup vacuously hit the "non-generic,
    // keep original" branch and silently no-op.
    op match {
      case AtomicOp.Tag(sym) =>
        AtomicOp.Tag(tolerant(lookupCaseSym(sym, rawResultTpe), sym))
      case AtomicOp.StructNew(sym, mutability, fields) =>
        val newStructSym = tolerant(lookupStructSym(sym, rawResultTpe), sym)
        AtomicOp.StructNew(newStructSym, mutability, fields.map(f => new Symbol.StructFieldSym(newStructSym, f.name, f.loc)))
      case AtomicOp.StructGet(sym) =>
        val newStructSym = tolerant(lookupStructSym(sym.structSym, exps.head.tpe), sym.structSym)
        AtomicOp.StructGet(new Symbol.StructFieldSym(newStructSym, sym.name, sym.loc))
      case AtomicOp.StructPut(sym) =>
        val newStructSym = tolerant(lookupStructSym(sym.structSym, exps.head.tpe), sym.structSym)
        AtomicOp.StructPut(new Symbol.StructFieldSym(newStructSym, sym.name, sym.loc))
      case other => other
    }
  }

  private def rewriteExpr(exp0: MonoAst.Expr)(implicit ctx: Context): MonoAst.Expr = exp0 match {
    case MonoAst.Expr.Cst(cst, tpe, loc) => MonoAst.Expr.Cst(cst, rewriteEnumStructType(tpe), loc)
    case MonoAst.Expr.Var(sym, tpe, loc) => MonoAst.Expr.Var(sym, rewriteEnumStructType(tpe), loc)
    case MonoAst.Expr.Lambda(fparam, exp, tpe, loc) =>
      MonoAst.Expr.Lambda(rewriteFormalParam(fparam), rewriteExpr(exp), rewriteEnumStructType(tpe), loc)
    case MonoAst.Expr.ApplyAtomic(op, exps, tpe, eff, loc) =>
      MonoAst.Expr.ApplyAtomic(rewriteAtomicOp(op, exps, tpe), exps.map(rewriteExpr), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.ApplyClo(exp1, exp2, tpe, eff, loc) =>
      MonoAst.Expr.ApplyClo(rewriteExpr(exp1), rewriteExpr(exp2), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.ApplyDef(sym, exps, itpe, tpe, eff, loc) =>
      MonoAst.Expr.ApplyDef(sym, exps.map(rewriteExpr), rewriteEnumStructType(itpe), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.ApplyLocalDef(sym, exps, tpe, eff, loc) =>
      MonoAst.Expr.ApplyLocalDef(sym, exps.map(rewriteExpr), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.ApplyOp(sym, exps, tpe, eff, loc) =>
      MonoAst.Expr.ApplyOp(sym, exps.map(rewriteExpr), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.Let(sym, exp1, exp2, tpe, eff, occur, loc) =>
      MonoAst.Expr.Let(sym, rewriteExpr(exp1), rewriteExpr(exp2), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), occur, loc)
    case MonoAst.Expr.LocalDef(sym, fparams, exp1, exp2, tpe, eff, occur, loc) =>
      MonoAst.Expr.LocalDef(sym, fparams.map(rewriteFormalParam), rewriteExpr(exp1), rewriteExpr(exp2), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), occur, loc)
    case MonoAst.Expr.Region(sym, regSym, exp, tpe, eff, loc) =>
      MonoAst.Expr.Region(sym, regSym, rewriteExpr(exp), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) =>
      MonoAst.Expr.IfThenElse(rewriteExpr(exp1), rewriteExpr(exp2), rewriteExpr(exp3), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.Stm(exps, exp, tpe, eff, loc) =>
      MonoAst.Expr.Stm(exps.map(rewriteExpr), rewriteExpr(exp), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.Discard(exp, eff, loc) =>
      MonoAst.Expr.Discard(rewriteExpr(exp), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.Match(exp, rules, tpe, eff, loc) =>
      MonoAst.Expr.Match(rewriteExpr(exp), rules.map(rewriteMatchRule), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.ExtMatch(exp, rules, tpe, eff, loc) =>
      MonoAst.Expr.ExtMatch(rewriteExpr(exp), rules.map(rewriteExtMatchRule), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.VectorLit(exps, tpe, eff, loc) =>
      MonoAst.Expr.VectorLit(exps.map(rewriteExpr), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.VectorLoad(exp1, exp2, tpe, eff, loc) =>
      MonoAst.Expr.VectorLoad(rewriteExpr(exp1), rewriteExpr(exp2), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.VectorLength(exp, loc) =>
      MonoAst.Expr.VectorLength(rewriteExpr(exp), loc)
    case MonoAst.Expr.Cast(exp, tpe, eff, loc) =>
      MonoAst.Expr.Cast(rewriteExpr(exp), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.TryCatch(exp, rules, tpe, eff, loc) =>
      MonoAst.Expr.TryCatch(rewriteExpr(exp), rules.map(rewriteCatchRule), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.RunWith(exp, effUse, rules, tpe, eff, loc) =>
      MonoAst.Expr.RunWith(rewriteExpr(exp), effUse, rules.map(rewriteHandlerRule), rewriteEnumStructType(tpe), rewriteEnumStructType(eff), loc)
    case MonoAst.Expr.NewObject(sym, clazz, tpe, eff, constructors, methods, loc) =>
      MonoAst.Expr.NewObject(sym, clazz, rewriteEnumStructType(tpe), rewriteEnumStructType(eff), constructors.map(rewriteJvmConstructor), methods.map(rewriteJvmMethod), loc)
  }

  private def rewritePattern(pat0: MonoAst.Pattern)(implicit ctx: Context): MonoAst.Pattern = pat0 match {
    case MonoAst.Pattern.Wild(tpe, loc) => MonoAst.Pattern.Wild(rewriteEnumStructType(tpe), loc)
    case MonoAst.Pattern.Var(sym, tpe, occur, loc) => MonoAst.Pattern.Var(sym, rewriteEnumStructType(tpe), occur, loc)
    case MonoAst.Pattern.Cst(cst, tpe, loc) => MonoAst.Pattern.Cst(cst, rewriteEnumStructType(tpe), loc)
    case MonoAst.Pattern.Tag(symUse, pats, tpe, loc) =>
      val newSym = tolerant(lookupCaseSym(symUse.sym, tpe), symUse.sym)
      MonoAst.Pattern.Tag(symUse.copy(sym = newSym), pats.map(rewritePattern), rewriteEnumStructType(tpe), loc)
    case MonoAst.Pattern.Tuple(pats, tpe, loc) =>
      MonoAst.Pattern.Tuple(pats.map(rewritePattern), rewriteEnumStructType(tpe), loc)
    case MonoAst.Pattern.Record(pats, pat, tpe, loc) =>
      val ps = pats.map(p => p.copy(pat = rewritePattern(p.pat), tpe = rewriteEnumStructType(p.tpe)))
      MonoAst.Pattern.Record(ps, rewritePattern(pat), rewriteEnumStructType(tpe), loc)
  }

  private def rewriteExtPattern(pat0: MonoAst.ExtPattern)(implicit ctx: Context): MonoAst.ExtPattern = pat0 match {
    case MonoAst.ExtPattern.Default(loc) => MonoAst.ExtPattern.Default(loc)
    case MonoAst.ExtPattern.Tag(label, pats, loc) => MonoAst.ExtPattern.Tag(label, pats.map(rewriteExtTagPattern), loc)
  }

  private def rewriteExtTagPattern(pat0: MonoAst.ExtTagPattern)(implicit ctx: Context): MonoAst.ExtTagPattern = pat0 match {
    case MonoAst.ExtTagPattern.Wild(tpe, loc) => MonoAst.ExtTagPattern.Wild(rewriteEnumStructType(tpe), loc)
    case MonoAst.ExtTagPattern.Var(sym, tpe, occur, loc) => MonoAst.ExtTagPattern.Var(sym, rewriteEnumStructType(tpe), occur, loc)
    case MonoAst.ExtTagPattern.Unit(tpe, loc) => MonoAst.ExtTagPattern.Unit(rewriteEnumStructType(tpe), loc)
  }

  private def rewriteMatchRule(rule: MonoAst.MatchRule)(implicit ctx: Context): MonoAst.MatchRule =
    MonoAst.MatchRule(rewritePattern(rule.pat), rule.guard.map(rewriteExpr), rewriteExpr(rule.exp))

  private def rewriteExtMatchRule(rule: MonoAst.ExtMatchRule)(implicit ctx: Context): MonoAst.ExtMatchRule =
    MonoAst.ExtMatchRule(rewriteExtPattern(rule.pat), rewriteExpr(rule.exp), rule.loc)

  private def rewriteCatchRule(rule: MonoAst.CatchRule)(implicit ctx: Context): MonoAst.CatchRule =
    rule.copy(exp = rewriteExpr(rule.exp))

  private def rewriteHandlerRule(rule: MonoAst.HandlerRule)(implicit ctx: Context): MonoAst.HandlerRule =
    MonoAst.HandlerRule(rule.op, rule.fparams.map(rewriteFormalParam), rewriteExpr(rule.exp))

  private def rewriteJvmConstructor(c: MonoAst.JvmConstructor)(implicit ctx: Context): MonoAst.JvmConstructor =
    MonoAst.JvmConstructor(rewriteExpr(c.exp), rewriteEnumStructType(c.retTpe), rewriteEnumStructType(c.eff), c.loc)

  private def rewriteJvmMethod(m: MonoAst.JvmMethod)(implicit ctx: Context): MonoAst.JvmMethod =
    m.copy(fparams = m.fparams.map(rewriteFormalParam), exp = rewriteExpr(m.exp))

  /**
    * Effect operations (`MonoAst.Op`, e.g. `Env.getArgs`'s own declared signature) also carry a
    * `Spec` — same shape as a def's — and, like defs, their embedded types can reference a
    * specialized enum/struct via a case/handler body elsewhere that HAS gone through
    * `rewriteDef`. Missing this specifically caused `Sys/Env.flix`'s `Env.getArgs` handler to
    * disagree with its own operation's declared type (one side rewritten via a def's body, the
    * effect operation's own signature not) — confirmed via `Test.Exp.Struct.Get.flix`'s
    * `TypeVerifier` failure citing exactly that mismatch.
    */
  private def rewriteEffect(eff: MonoAst.Effect)(implicit ctx: Context): MonoAst.Effect =
    eff.copy(ops = eff.ops.map(op => op.copy(spec = rewriteSpec(op.spec))))

  // ---- run -------------------------------------------------------------------

  def run(root: TypedAst.Root, solution: Solution)(implicit flix: Flix): MonoAst.Root = flix.phase("Monomorpher") {
    implicit val r: TypedAst.Root = root
    implicit val is: Map[(Symbol.TraitSym, TypeConstructor), Instance] = MonomorphCanon.mkInstanceMap(root.instances)

    // Instance defs live in root.instances, not root.defs — merge for unified lookup.
    // Also track which instance each def belongs to, so we can use inst.tparams when building subst.
    val allInstanceDefs: Map[Symbol.DefnSym, TypedAst.Def] =
      root.instances.values.flatMap(_.defs).map(d => d.sym -> d).toMap
    // Map from instance-def sym → its owning Instance (for inst.tparams lookup).
    val defToInst: Map[Symbol.DefnSym, TypedAst.Instance] =
      root.instances.values.flatMap(inst => inst.defs.map(d => d.sym -> inst)).toMap
    // Default sig implementations: sig.exp defines the body at the trait level.
    // Build synthetic TypedAst.Def entries using the same sym formula as ConstraintCollection/Solver.
    // Also track each default-sig-sym → the trait's own tparams (not in sig.spec.tparams).
    // The solver tuple for a default sig impl is [traitType, ...sig-own args], so the trait
    // tparams must be prepended when building the substMap in entries below.
    val defaultSigDefs: Map[Symbol.DefnSym, TypedAst.Def] =
      root.sigs.values.flatMap { sig =>
        sig.exp.map { exp =>
          val ns      = sig.sym.trt.namespace :+ sig.sym.trt.name
          val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
          defnSym -> TypedAst.Def(defnSym, sig.spec, exp, sig.sym.loc)
        }
      }.toMap
    // Maps each default-sig-sym to the trait's own tparams (not in sig.spec.tparams).
    val defaultSigTraitTparams: Map[Symbol.DefnSym, List[TypedAst.TypeParam]] =
      root.sigs.values.flatMap { sig =>
        sig.exp.map { _ =>
          val ns      = sig.sym.trt.namespace :+ sig.sym.trt.name
          val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
          defnSym -> List(root.traits(sig.sym.trt).tparam)
        }
      }.toMap

    val allDefs: Map[Symbol.DefnSym, TypedAst.Def] = root.defs ++ allInstanceDefs ++ defaultSigDefs

    // Build entries: one per (sym, tuple) pair from the solution for parametric defs.
    //
    // Solver tuple ordering for instance defs:
    //   [inst.tparams values..., sig-own tparams values...]
    // where the prefix covers the instance's tparams (free vars in spec.declaredScheme.base)
    // and the suffix covers spec.tparams (the def's own declared tparams).
    // A speculative tuple the solver proposes (e.g. a stray Star var defaulted to AnyType) can
    // require an instance that doesn't exist (e.g. Coerce[AnyType]) — StrictSubstitution.mk or
    // subst(declaredScheme.base) then throws InternalCompilerException while reducing an
    // associated type. Compute both here, together, and drop just this one (sym, tuple) pair on
    // failure rather than letting the exception propagate out of the for-comprehension and abort
    // every other def's entries — same outcome as "the solver never proposed this tuple," just
    // reached by attempting the real reduction instead of predicting it up front.
    val entries: List[(Symbol.DefnSym, TypedAst.Def, StrictSubstitution, Type)] =
      for {
        (sym, tuples)  <- solution.defs.toList
        defn           <- allDefs.get(sym).toList
        tuple          <- tuples.toList
        instTparams     = defToInst.get(sym).map(_.tparams).getOrElse(Nil)
        // For default sig impls the trait's tparam(s) are prepended in the solver tuple
        // but NOT in defn.spec.tparams; recover them from defaultSigTraitTparams.
        traitTparams    = defaultSigTraitTparams.getOrElse(sym, Nil)
        // inst.tparams are free vars in the scheme — pair with the tuple prefix.
        // traitTparams cover the trait's own params (default sigs only).
        // spec.tparams are the def's own generics — pair with the tuple suffix.
        prefixTparams   = instTparams ++ traitTparams
        substMap        = (prefixTparams.zip(tuple) ++ defn.spec.tparams.zip(tuple.drop(prefixTparams.length)))
                            .map { case (tp, ty) => tp.sym -> ty }.toMap
        if defn.spec.tparams.nonEmpty || instTparams.nonEmpty || traitTparams.nonEmpty
        freshSym        = Symbol.freshDefnSym(defn.sym)
        (subst, it)     <- try {
                             val s = StrictSubstitution.mk(Substitution(substMap))
                             List((s, s(defn.spec.declaredScheme.base)))
                           } catch {
                             case _: InternalCompilerException => Nil
                           }
      } yield (freshSym, defn, subst, it)

    // defTable: (original sym, instantiated arrow type) → fresh specialized sym.
    val defTableMap: Map[(Symbol.DefnSym, Type), Symbol.DefnSym] =
      entries.map { case (freshSym, defn, _, it) => (defn.sym, it) -> freshSym }.toMap

    // Build enum/struct entries: one per (sym, tuple) pair from the solution, for enums/structs
    // with a nonempty tparams list (non-generic ones need no specialization at all — see
    // lookupCaseSym/lookupStructSym's "argTypes.isEmpty" case, which keeps the original sym).
    //
    // Specialize wrt. primitive types only, per-position (design settled with Magnus/refined by
    // Simon, see notes/design_questions.md's "✅ Resolved by Magnus directly"): each type argument
    // is judged independently. Solved tuples are grouped by their "signature" — primitive
    // arguments kept exact, non-primitive arguments collapsed to a single AnyType marker purely
    // for grouping — so e.g. Result[Int32, String] and Result[Int32, Option[Int32]] share one
    // declaration (position 0 pinned to Int32, position 1 stays generic), while Result[String,
    // Int32] gets a different one (position 1 pinned instead). A tuple with *no* primitive
    // argument at all (e.g. Result[String, String]) is dropped entirely — nothing would be
    // pinned, so it's the same as the original declaration; `lookupCaseSym`/`lookupStructSym`'s
    // "keep original" fallback (`!argTypes.exists(isPrimitive)`) covers exactly this case.
    val enumEntries: List[(Symbol.EnumSym, List[Type], Symbol.EnumSym, TypedAst.Enum)] =
      for {
        (sym, tuples) <- solution.enums.toList
        enm           <- root.enums.get(sym).toList
        if enm.tparams.nonEmpty
        (signature, exactTuples) <- tuples.toList.groupBy(specializationSignature).toList
        if signature.exists(MonomorphCanon.isPrimitive)
        freshSym       = Symbol.freshEnumSym(enm.sym)
        (substMap, survivingTparams) = partialSubst(enm.tparams, signature)
        newEnum        = {
                           val newCases = enm.cases.map { case (caseSym, TypedAst.Case(_, tpes, sc, cloc)) =>
                             val newCaseSym = new Symbol.CaseSym(freshSym, caseSym.name, caseSym.ordinal, caseSym.loc)
                             val newTpes = tpes.map(t => MonomorphCanon.simplify(Substitution(substMap)(t), isGround = false))
                             newCaseSym -> TypedAst.Case(newCaseSym, newTpes, sc, cloc)
                           }
                           TypedAst.Enum(enm.doc, enm.ann, enm.mod, freshSym, survivingTparams, enm.derives, newCases, enm.loc)
                         }
        exactTuple    <- exactTuples
      } yield (sym, exactTuple, freshSym, newEnum)

    val enumTableMap: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym] =
      enumEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    val structEntries: List[(Symbol.StructSym, List[Type], Symbol.StructSym, TypedAst.Struct)] =
      for {
        (sym, tuples) <- solution.structs.toList
        struct        <- root.structs.get(sym).toList
        if struct.tparams.nonEmpty
        (signature, exactTuples) <- tuples.toList.groupBy(specializationSignature).toList
        if signature.exists(MonomorphCanon.isPrimitive)
        freshSym       = Symbol.freshStructSym(struct.sym)
        (substMap, survivingTparams) = partialSubst(struct.tparams, signature)
        newStruct      = {
                           val newFields = struct.fields.map { case (fieldSym, TypedAst.StructField(_, tpe, floc)) =>
                             val newFieldSym = new Symbol.StructFieldSym(freshSym, fieldSym.name, fieldSym.loc)
                             val newTpe = MonomorphCanon.simplify(Substitution(substMap)(tpe), isGround = false)
                             newFieldSym -> TypedAst.StructField(newFieldSym, newTpe, floc)
                           }
                           TypedAst.Struct(struct.doc, struct.ann, struct.mod, freshSym, survivingTparams, struct.sc, newFields, struct.loc)
                         }
        exactTuple    <- exactTuples
      } yield (sym, exactTuple, freshSym, newStruct)

    val structTableMap: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym] =
      structEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    implicit val ctx: Context = new Context(defTableMap, allDefs, enumTableMap, structTableMap)

    // Non-parametric defs: those with no spec.tparams AND no instance tparams AND not a
    // default-sig impl (which has trait tparams not in spec.tparams — always goes via entries).
    ParOps.parMap(allDefs.filter { case (sym, d) =>
      d.spec.tparams.isEmpty &&
      defToInst.get(sym).map(_.tparams.isEmpty).getOrElse(true) &&
      !defaultSigDefs.contains(sym)
    }) {
      case (sym, defn) => flix.profile(defn.sym, defn.loc) {
        ctx.addSpecializedDef(sym, rewriteDef(SolutionLowering.lowerDef(specializeDef(sym, defn, StrictSubstitution.empty))))
      }
    }

    // Parametric specializations — one parallel pass, no worklist loop.
    ParOps.parMap(entries) { case (freshSym, defn, subst, _) =>
      flix.profile(defn.sym, defn.loc) {
        ctx.addSpecializedDef(freshSym, rewriteDef(SolutionLowering.lowerDef(specializeDef(freshSym, defn, subst))))
      }
    }

    val effects = ParOps.parMapValues(root.effects) {
      case TypedAst.Effect(doc, ann, mod, sym, targs, ops0, loc) =>
        val ops = ops0.map(visitEffectOp)
        rewriteEffect(SolutionLowering.lowerEffect(TypedAst.Effect(doc, ann, mod, sym, targs, ops, loc)))
    }

    // Kept as-is (one polymorphic declaration per original enum/struct), same as before this
    // feature existed — NOT replaced by the specialized declarations below, added alongside
    // instead. Two reasons this is additive, not exclusive: (1) some enum/struct constructions
    // are synthesized directly as MonoAst by SolutionLowering (e.g. the Datalog Fixpoint3.Ast.*
    // enums built by mkTag), never passing through specializeExp's Expr.Tag/StructNew rewriting
    // at all — those references still need the original, polymorphic declaration to resolve
    // against; (2) it costs nothing to keep an unused original declaration around alongside a
    // specialized one, and doing so is strictly safer than trying to prove it is never needed.
    val enums = ParOps.parMapValues(root.enums) {
      case TypedAst.Enum(doc, ann, mod, sym, tparams0, derives, cases, loc) =>
        val tparams = tparams0.map { case TypedAst.TypeParam(name, sym, loc) => TypedAst.TypeParam(name, sym, loc) }
        SolutionLowering.lowerEnum(TypedAst.Enum(doc, ann, mod, sym, tparams, derives, MapOps.mapValues(cases)(visitEnumCase), loc))
    }

    // One specialized declaration (fresh sym, renamed cases, ground field types, tparams = Nil)
    // per (sym, tuple) the solver actually found reachable — see enumEntries above and
    // lookupCaseSym, which is what makes expressions actually reference these fresh syms.
    val specializedEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(enumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SolutionLowering.lowerEnum(newEnum) }.toMap

    val restrictableEnums = ParOps.parMapValues(root.restrictableEnums) {
      case TypedAst.RestrictableEnum(doc, ann, mod, sym, index, tparams0, derives, cases, loc) =>
        val tparams = tparams0.map { case TypedAst.TypeParam(name, sym, loc) => TypedAst.TypeParam(name, sym, loc) }
        SolutionLowering.lowerRestrictableEnum(TypedAst.RestrictableEnum(doc, ann, mod, sym, index, tparams, derives, MapOps.mapValues(cases)(visitRestrictableEnumCase), loc))
    }

    val structs = ParOps.parMapValues(root.structs) {
      case TypedAst.Struct(doc, ann, mod, sym, tparams0, sc, fields, loc) =>
        val tparams = tparams0.map { case TypedAst.TypeParam(name, sym, loc) => TypedAst.TypeParam(name, sym, loc) }
        SolutionLowering.lowerStruct(TypedAst.Struct(doc, ann, mod, sym, tparams, sc, MapOps.mapValues(fields)(visitStructField), loc))
    }

    val specializedStructs: Map[Symbol.StructSym, MonoAst.Struct] =
      ParOps.parMap(structEntries) { case (_, _, freshSym, newStruct) => freshSym -> SolutionLowering.lowerStruct(newStruct) }.toMap

    MonoAst.Root(
      ctx.getSpecializedDefs,
      enums ++ specializedEnums ++ restrictableEnums.map { case (_, v) => v.sym -> v },
      structs ++ specializedStructs,
      effects,
      root.mainEntryPoint,
      root.entryPoints,
      root.sources
    )
  }
}
