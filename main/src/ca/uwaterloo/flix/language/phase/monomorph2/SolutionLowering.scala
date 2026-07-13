/*
 * Copyright 2021 Magnus Madsen
 *           2025 Casper Dalgaard Nielsen
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
import ca.uwaterloo.flix.language.ast.TypedAst.{DefaultHandler, Predicate}
import ca.uwaterloo.flix.language.ast.MonoAst.{DefContext, Occur}
import ca.uwaterloo.flix.language.ast.ops.TypedAstOps
import ca.uwaterloo.flix.language.ast.TypedAst.ApplyPosition
import ca.uwaterloo.flix.language.ast.shared.{BoundBy, Constant, Decreasing, Denotation, Fixity, Mutability, Polarity, PredicateAndArity, RegionScope, SolveMode, SymUse, TypeSource}
import ca.uwaterloo.flix.language.ast.{AtomicOp, MonoAst, Name, SemanticOp, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.phase.monomorph2.SolutionSpecialization.{Context, StrictSubstitution, lookupCaseSym, lookupStructSym, lookupSym, resolveSigSym, specializeFormalParam, specializeFormalParams}
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.{Defs, Enums, Types}
import ca.uwaterloo.flix.util.{InternalCompilerException, JvmUtils, Result}
import ca.uwaterloo.flix.util.collection.{CofiniteSet, ListOps, Nel}

/**
  * This phase translates AST expressions related to the Datalog subset of the
  * language into `Fixpoint.Ast.Datalog` values (which are ordinary Flix values).
  * This allows the Datalog engine to be implemented as an ordinary Flix program.
  *
  * In addition to translating expressions, types must also be translated from
  * Schema types to enum types.
  *
  * Finally, values must be boxed using the Boxable.
  *
  * It also translates channels to the lowered types.
  */
object SolutionLowering {

  /**
    * Lowers the given type `tpe0`.
    *
    * Replaces schema types with the Datalog enum type and channel-related types with the channel enum type.
    */
  private def lowerType(tpe0: Type): Type = tpe0.typeConstructor match {
    case Some(TypeConstructor.Schema) =>
      // LOWERING: Schema type → erased Datalog enum type.
      // We replace any Schema type, no matter the number of polymorphic type applications, with the erased Datalog type.
      Types.Datalog
    case _ => lowerTypeNonSchema(tpe0)
  }

  private def lowerTypeNonSchema(tpe0: Type): Type = tpe0 match {
    case Type.Cst(_, _) => tpe0 // Performance: Reuse tpe0.

    case Type.Var(_, _) => tpe0

    // LOWERING: Sender[t] → Concurrent.Channel.Mpmc[t, IO]
    case Type.Apply(Type.Cst(TypeConstructor.Sender, loc), tpe, _) =>
      val t = lowerType(tpe)
      mkChannelTpe(t, loc)

    // LOWERING: Receiver[t] → Concurrent.Channel.Mpmc[t, IO]
    case Type.Apply(Type.Cst(TypeConstructor.Receiver, loc), tpe, _) =>
      val t = lowerType(tpe)
      mkChannelTpe(t, loc)

    case Type.Apply(tpe1, tpe2, loc) =>
      val t1 = lowerType(tpe1)
      val t2 = lowerType(tpe2)
      // Performance: Reuse tpe0, if possible.
      if ((t1 eq tpe1) && (t2 eq tpe2)) {
        tpe0
      } else {
        Type.Apply(t1, t2, loc)
      }

    case Type.Alias(sym, args, t, loc) =>
      Type.Alias(sym, args.map(lowerType), lowerType(t), loc)

    case Type.AssocType(_, _, _, loc) => throw InternalCompilerException("unexpected associated type", loc)

    case Type.JvmToType(_, loc) => throw InternalCompilerException("unexpected JVM type", loc)

    case Type.JvmToEff(_, loc) => throw InternalCompilerException("unexpected JVM eff", loc)

    case Type.UnresolvedJvmType(_, loc) => throw InternalCompilerException("unexpected JVM type", loc)

  }

  /**
    * Composes substitution, lowering, and the enum/struct-type rewrite (`SolutionSpecialization.rewriteEnumStructType`)
    * into the single call every type in the fused walk goes through.
    */
  private def visitType(t: Type, subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): Type =
    SolutionSpecialization.rewriteEnumStructType(lowerType(subst(t)))

  /**
    * Same as `visitType`, for the handful of call sites where the caller already applied `subst`
    * (the value arrives pre-substituted, e.g. `visitExp`'s `FixpointQueryWithProvenance` case
    * passes `subst(tpe0)` into `lowerQueryWithProvenance`) — only lowering + the rewrite remain.
    */
  private def visitTypeSubstituted(t: Type)(implicit ctx: Context): Type =
    SolutionSpecialization.rewriteEnumStructType(lowerType(t))

  /**
    * Specializes and lowers the given def `defn0` under `subst` in one fused walk, producing the
    * final `MonoAst.Def` for the specialized symbol `freshSym`. Fusing specialization and lowering
    * into a single walk avoids materializing an intermediate TypedAst that would otherwise be
    * discarded immediately.
    */
  protected[monomorph2] def visitDef(freshSym: Symbol.DefnSym, defn0: TypedAst.Def, subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Def = {
    implicit val lctx: LocalContext = LocalContext.empty
    /*
     LOWERING: entry-point default-handler wrapping.
     If the definition is an entry point it is wrapped with the required default handlers before the rest of lowering.
       For example:
          {{{ def myEntryPoint(): Unit \ Assert = e }}}
       Will be transformed into:
          {{{ def myEntryPoint(): Unit \ IO = Assert.runWithIO(_ -> e) }}}
     Entry points are non-parametric, so `subst` is empty here — but applying it to the spec's
     types first still matters: it canonicalizes them, and wrapInHandler builds defTable lookup
     keys from these fields (defTable keys are canonical — see wrapInHandler's own comment).
     */
    val defn = if (TypedAstOps.isEntryPoint(defn0)) {
      val spec0 = defn0.spec
      val spec = spec0.copy(
        fparams = spec0.fparams.map(fp => fp.copy(tpe = subst(fp.tpe))),
        declaredScheme = spec0.declaredScheme.copy(base = subst(spec0.declaredScheme.base)),
        retTpe = subst(spec0.retTpe),
        eff = subst(spec0.eff)
      )
      wrapDefWithDefaultHandlers(defn0.copy(spec = spec))
    } else {
      defn0
    }
    try {
      defn match {
        case TypedAst.Def(_, spec0, exp, loc) =>
          val (fparams, env0) = specializeFormalParams(spec0.fparams, subst)
          val fs = fparams.map(lowerFormalParam).map(SolutionSpecialization.rewriteFormalParam)
          val spec = spec0 match {
            case TypedAst.Spec(doc, ann, mod, _, _, declaredScheme, retTpe, eff, _, _) =>
              // `eff` is substituted but deliberately not lowered: this phase does not lower effects.
              MonoAst.Spec(doc, ann, mod, fs, visitType(declaredScheme.base, subst), visitType(retTpe, subst), subst(eff), DefContext.Unknown)
          }
          val e = visitExp(exp, env0, subst)
          MonoAst.Def(freshSym, spec, e, loc)
      }
    } catch {
      case e: InternalCompilerException =>
        throw InternalCompilerException(s"[in ${defn.sym} (subst: $subst)]: ${e.message}", e.loc)
    }
  }

  /**
    * Lowers the given enum `enum0`.
    */
  protected[monomorph2] def lowerEnum(enum0: TypedAst.Enum): MonoAst.Enum = enum0 match {
    case TypedAst.Enum(doc, ann, mod, sym, tparams0, _, cases0, loc) =>
      val tparams = tparams0.map(lowerTypeParam)
      val cases = cases0.map {
        case (_, TypedAst.Case(caseSym, tpes0, _, caseLoc)) =>
          val tpes = tpes0.map(lowerType)
          (caseSym, MonoAst.Case(caseSym, tpes, caseLoc))
      }
      MonoAst.Enum(doc, ann, mod, sym, tparams, cases, loc)
  }

  /**
    * Lowers the given enum `enum0` from a restrictable enum into a regular enum.
    */
  protected[monomorph2] def lowerRestrictableEnum(enum0: TypedAst.RestrictableEnum): MonoAst.Enum = enum0 match {
    case TypedAst.RestrictableEnum(doc, ann, mod, sym0, index0, tparams0, _, cases0, loc) =>
      // index is erased since related checking has concluded.
      // Restrictable tag is lowered into a regular tag
      val index = lowerTypeParam(index0)
      val tparams = tparams0.map(lowerTypeParam)
      val cases = cases0.map {
        case (_, TypedAst.RestrictableCase(caseSym0, tpes0, _, caseLoc)) =>
          val tpes = tpes0.map(lowerType)
          val caseSym = lowerRestrictableCaseSym(caseSym0)
          (caseSym, MonoAst.Case(caseSym, tpes, caseLoc))
      }
      val sym = lowerRestrictableEnumSym(sym0)
      MonoAst.Enum(doc, ann, mod, sym, index :: tparams, cases, loc)
  }

  /**
    * Lowers the given `effect`.
    */
  protected[monomorph2] def lowerEffect(effect: TypedAst.Effect): MonoAst.Effect = effect match {
    case TypedAst.Effect(doc, ann, mod, sym, _, ops0, loc) =>
      // TODO EFFECT-TPARAMS use tparams
      val ops = ops0.map(lowerOp)
      MonoAst.Effect(doc, ann, mod, sym, ops, loc)
  }

  /**
    * Lowers the given struct `struct0`.
    */
  protected[monomorph2] def lowerStruct(struct0: TypedAst.Struct): MonoAst.Struct = struct0 match {
    case TypedAst.Struct(doc, ann, mod, sym, tparams0, _, fields0, loc) =>
      val tparams = tparams0.map(lowerTypeParam)
      val fields = fields0.map {
        case (fieldSym, field) => MonoAst.StructField(fieldSym, lowerType(field.tpe), loc)
      }
      MonoAst.Struct(doc, ann, mod, sym, tparams, fields.toList, loc)
  }

  /**
    * Lowers the given `op`.
    */
  private def lowerOp(op: TypedAst.Op): MonoAst.Op = op match {
    case TypedAst.Op(sym, spec0, loc) =>
      val spec = lowerSpec(spec0)
      MonoAst.Op(sym, spec, loc)
  }

  /**
    * Lowers the given `spec0`.
    */
  private def lowerSpec(spec0: TypedAst.Spec): MonoAst.Spec = spec0 match {
    case TypedAst.Spec(doc, ann, mod, _, fparams0, declaredScheme, retTpe, eff, _, _) =>
      val fs = fparams0.map(lowerFormalParam)
      val fType = lowerType(declaredScheme.base)
      val rType = lowerType(retTpe)
      MonoAst.Spec(doc, ann, mod, fs, fType, rType, eff, DefContext.Unknown)
  }

  /**
    * Specializes and lowers `exp0` in one fused walk:
    *   - variables are renamed via `env0` (fresh syms, unique per specialization copy),
    *   - every type is ground-instantiated via `subst` (the solver-provided substitution),
    *   - def/sig/case/struct symbols are resolved against the solver solution (strict: a miss is
    *     a "Solver gap" crash),
    *   - types are lowered and channel/fixpoint expressions are lowered to the primitives.
    *
    * Cases marked `// LOWERING:` perform a genuine lowering transformation (output structurally
    * different from the input); everything else is specialization plus structural mapping.
    */
  private def visitExp(exp0: TypedAst.Expr, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = exp0 match {
    case TypedAst.Expr.Cst(cst, tpe, loc) => MonoAst.Expr.Cst(cst, visitType(tpe, subst), loc)

    case TypedAst.Expr.Var(sym, tpe, loc) => MonoAst.Expr.Var(env0(sym), visitType(tpe, subst), loc)

    case TypedAst.Expr.Hole(sym, _, tpe, eff, loc) =>
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.HoleError(sym), List.empty, t, subst(eff), loc)

    case TypedAst.Expr.HoleWithExp(_, _, tpe, _, loc) =>
      val sym = Symbol.freshHoleSym(loc)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.HoleError(sym), List.empty, t, Type.Pure, loc)

    case TypedAst.Expr.OpenAs(_, exp, _, _) =>
      visitExp(exp, env0, subst) // TODO RESTR-VARS maybe add to monoAST

    case TypedAst.Expr.Use(_, _, exp, _) =>
      visitExp(exp, env0, subst)

    case TypedAst.Expr.Lambda(fparam, exp, tpe, loc) =>
      val (fp, env1) = specializeFormalParam(fparam, subst)
      val p = SolutionSpecialization.rewriteFormalParam(lowerFormalParam(fp))
      val e = visitExp(exp, env0 ++ env1, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.Lambda(p, e, t, loc)

    case TypedAst.Expr.ApplyClo(exp1, exp2, tpe, eff, _, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyClo(e1, e2, t, subst(eff), loc)

    case TypedAst.Expr.ApplyDef(symUse, exps, _, itpe, tpe, eff, _, loc) =>
      // The instantiated arrow type is the solver-solution lookup key: keyed PRE-lowering.
      val it = subst(itpe)
      val newSym = lookupSym(symUse.sym, it)
      val es = exps.map(visitExp(_, env0, subst))
      MonoAst.Expr.ApplyDef(newSym, es, visitTypeSubstituted(it), visitType(tpe, subst), subst(eff), loc)

    case TypedAst.Expr.ApplyLocalDef(symUse, exps, _, tpe, eff, _, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyLocalDef(env0(symUse.sym), es, t, subst(eff), loc)

    case TypedAst.Expr.ApplyOp(symUse, exps, tpe, eff, _, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyOp(symUse.sym, es, t, subst(eff), loc)

    case TypedAst.Expr.Unary(sop, exp, tpe, eff, loc) => sop match {
      // ReflectOps are resolved here, at specialization time: the reflected type is only known
      // once `subst` has grounded it. (Specialization-time expansion, not a lowering transform.)
      case SemanticOp.ReflectOp.ReflectEff =>
        val expTpe = subst(exp.tpe)
        val typeArg = expTpe.typeArguments.headOption.getOrElse(
          throw InternalCompilerException(s"Expected ProxyEff[ef] type, got $expTpe", loc))
        val purityEnumSym = Enums.Purity
        val caseName = typeArg match {
          case Type.Cst(TypeConstructor.Pure, _) => "Pure"
          case _                                 => "Impure"
        }
        val caseSym = findCaseSym(purityEnumSym, caseName)
        MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(caseSym), Nil, Type.mkEnum(purityEnumSym, Nil, loc), Type.Pure, loc)

      case SemanticOp.ReflectOp.ReflectType =>
        val expTpe = subst(exp.tpe)
        val typeArg = expTpe.typeArguments.headOption.getOrElse(
          throw InternalCompilerException(s"Expected Proxy[t] type, got $expTpe", loc))
        val jvmTypeEnumSym = Enums.JvmType
        val caseName = jvmTypeCaseName(typeArg.baseType)
        val caseSym = findCaseSym(jvmTypeEnumSym, caseName)
        MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(caseSym), Nil, Type.mkEnum(jvmTypeEnumSym, Nil, loc), Type.Pure, loc)

      case SemanticOp.ReflectOp.ReflectValue =>
        val e = visitExp(exp, env0, subst)
        val expTpe = subst(exp.tpe)
        val jvmValueEnumSym = Enums.JvmValue
        val resultType = Type.mkEnum(jvmValueEnumSym, Nil, loc)
        val caseName = jvmTypeCaseName(expTpe.baseType)
        val caseSym = findCaseSym(jvmValueEnumSym, caseName)
        val tagArg = if (caseName == "JvmObject") {
          val objType = Type.mkNative(classOf[java.lang.Object], loc)
          mkCast(e, objType, Type.Pure, loc)
        } else { e }
        MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(caseSym), List(tagArg), resultType, subst(eff), loc)

      case _ =>
        val e = visitExp(exp, env0, subst)
        val t = visitType(tpe, subst)
        MonoAst.Expr.ApplyAtomic(AtomicOp.Unary(sop), List(e), t, subst(eff), loc)
    }

    case TypedAst.Expr.Binary(sop, exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Binary(sop), List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.Let(bnd, exp1, exp2, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env1, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.Let(freshSym, e1, e2, t, subst(eff), Occur.Unknown, loc)

    case TypedAst.Expr.LocalDef(_, bnd, fparams, exp1, exp2, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      val (fparams1, env2) = specializeFormalParams(fparams, subst)
      val fps = fparams1.map(lowerFormalParam).map(SolutionSpecialization.rewriteFormalParam)
      val e1 = visitExp(exp1, env1 ++ env2, subst)
      val e2 = visitExp(exp2, env1, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.LocalDef(freshSym, fps, e1, e2, t, subst(eff), Occur.Unknown, loc)

    case TypedAst.Expr.Region(bnd, regSym, exp, tpe, eff, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      val e = visitExp(exp, env1, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.Region(freshSym, regSym, e, t, subst(eff), loc)

    case TypedAst.Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val e3 = visitExp(exp3, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.IfThenElse(e1, e2, e3, t, subst(eff), loc)

    case TypedAst.Expr.Stm(exps, exp, tpe, eff, loc) =>
      // LOWERING: strip auto-unboxing: `m.put("k", 42);` discards the result, so we must not
      // unbox the null that `HashMap.put` returns on first insert (would NPE).
      val es = exps.map(e => stripAutoUnbox(visitExp(e, env0, subst)))
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.Stm(es, e, t, subst(eff), loc)

    case TypedAst.Expr.Discard(exp, eff, loc) =>
      // LOWERING: strip auto-unboxing: same reason as Stm — discarded results must not be unboxed.
      val e = stripAutoUnbox(visitExp(exp, env0, subst))
      MonoAst.Expr.Discard(e, subst(eff), loc)

    case TypedAst.Expr.Match(exp, rules, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      val rs = rules.map(visitMatchRule(_, env0, subst))
      MonoAst.Expr.Match(e, rs, t, subst(eff), loc)

    case TypedAst.Expr.RestrictableChoose(_, exp, rules, tpe, eff, loc) =>
      // LOWERING: restrictable choose → ordinary match
      val e = visitExp(exp, env0, subst)
      val rs = rules.map(lowerRestrictableChooseRule(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.Match(e, rs, t, subst(eff), loc)

    case TypedAst.Expr.ExtMatch(exp, rules, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val rs = rules.map(lowerExtMatch(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ExtMatch(e, rs, t, subst(eff), loc)

    case TypedAst.Expr.Tag(symUse, exps, tpe, eff, loc) =>
      // The tag's own result type IS the enum's ground type at this construction site: the
      // solver-solution lookup key (pre-lowering). Strict: a miss is a Solver gap.
      val t = subst(tpe)
      val newSym = lookupCaseSym(symUse.sym, t)
      val es = exps.map(visitExp(_, env0, subst))
      MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(newSym), es, visitTypeSubstituted(t), subst(eff), loc)

    case TypedAst.Expr.RestrictableTag(symUse, exps, tpe, eff, loc) =>
      // LOWERING: restrictable tag → ordinary tag (restrictable enums are not specialized).
      val caseSym = lowerRestrictableCaseSym(symUse.sym)
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(caseSym), es, t, subst(eff), loc)

    case TypedAst.Expr.ExtTag(label, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ExtTag(label), es, t, subst(eff), loc)

    case TypedAst.Expr.Tuple(exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Tuple, es, t, subst(eff), loc)

    case TypedAst.Expr.RecordSelect(exp, label, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.RecordSelect(label), List(e), t, subst(eff), loc)

    case TypedAst.Expr.RecordExtend(label, exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.RecordExtend(label), List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.RecordRestrict(label, exp, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.RecordRestrict(label), List(e), t, subst(eff), loc)

    case TypedAst.Expr.ArrayLit(exps, exp, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ArrayLit, e :: es, t, subst(eff), loc)

    case TypedAst.Expr.ArrayNew(exp1, exp2, exp3, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val e3 = visitExp(exp3, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ArrayNew, List(e1, e2, e3), t, subst(eff), loc)

    case TypedAst.Expr.ArrayLoad(exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ArrayLoad, List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.ArrayLength(exp, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ArrayLength, List(e), Type.Int32, subst(eff), loc)

    case TypedAst.Expr.ArrayStore(exp1, exp2, exp3, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val e3 = visitExp(exp3, env0, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.ArrayStore, List(e1, e2, e3), Type.Unit, subst(eff), loc)

    case TypedAst.Expr.StructNew(sym, fields0, region0, tpe, eff, loc) =>
      // The StructNew's own result type IS the struct's ground type at this construction site:
      // the solver-solution lookup key (pre-lowering). Field syms are rebuilt against the
      // specialized struct sym.
      val t = subst(tpe)
      val newStructSym = lookupStructSym(sym, t)
      val fields = fields0.map { case (symUse, v) =>
        (new Symbol.StructFieldSym(newStructSym, symUse.sym.name, symUse.loc), visitExp(v, env0, subst))
      }
      val (names, es) = fields.unzip
      val tLow = visitTypeSubstituted(t)
      region0.map(visitExp(_, env0, subst)) match {
        case Some(region) =>
          MonoAst.Expr.ApplyAtomic(AtomicOp.StructNew(newStructSym, Mutability.Mutable, names), region :: es, tLow, subst(eff), loc)
        case None =>
          MonoAst.Expr.ApplyAtomic(AtomicOp.StructNew(newStructSym, Mutability.Immutable, names), es, tLow, subst(eff), loc)
      }

    case TypedAst.Expr.StructGet(exp, field, tpe, eff, loc) =>
      // Unlike Tag/StructNew (whose own result type IS the enum/struct type), StructGet's own
      // `tpe` is the FIELD's type — the struct being accessed is `exp`'s type instead.
      val e = visitExp(exp, env0, subst)
      val newStructSym = lookupStructSym(field.sym.structSym, subst(exp.tpe))
      val newFieldSym = new Symbol.StructFieldSym(newStructSym, field.sym.name, field.loc)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.StructGet(newFieldSym), List(e), t, subst(eff), loc)

    case TypedAst.Expr.StructPut(exp, field, exp1, tpe, eff, loc) =>
      val struct = visitExp(exp, env0, subst)
      val newStructSym = lookupStructSym(field.sym.structSym, subst(exp.tpe))
      val newFieldSym = new Symbol.StructFieldSym(newStructSym, field.sym.name, field.loc)
      val rhs = visitExp(exp1, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.StructPut(newFieldSym), List(struct, rhs), t, subst(eff), loc)

    case TypedAst.Expr.VectorLit(exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.VectorLit, es, t, subst(eff), loc)

    case TypedAst.Expr.VectorLoad(exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.VectorLoad, List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.VectorLength(exp, loc) =>
      val e = visitExp(exp, env0, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.VectorLength, List(e), Type.Int32, e.eff, loc)

    case TypedAst.Expr.Ascribe(exp, _, _, _, _, _) =>
      visitExp(exp, env0, subst)

    case TypedAst.Expr.InstanceOf(exp, clazz, loc) =>
      // LOWERING: instanceof on a primitive type → evaluate and return false
      val e = visitExp(exp, env0, subst)
      if (isPrimType(e.tpe)) {
        // If it's a primitive type, evaluate the expression but return false
        MonoAst.Expr.Stm(List(e), MonoAst.Expr.Cst(Constant.Bool(false), Type.Bool, loc), Type.Bool, e.eff, loc)
      } else {
        // If it's a reference type, then do the instanceof check
        MonoAst.Expr.ApplyAtomic(AtomicOp.InstanceOf(clazz), List(e), Type.Bool, e.eff, loc)
      }

    case TypedAst.Expr.CheckedCast(_, exp, tpe, eff, loc) =>
      // LOWERING: cast erasure (mkCast decides cast vs. bytecode-verifier crash)
      // Note: We do *NOT* erase checked (i.e. safe) casts.
      // In Java, `String` is a subtype of `Object`, but the Flix IR makes this upcast _explicit_.
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      mkCast(e, t, subst(eff), loc)

    case TypedAst.Expr.UncheckedCast(exp, _, _, tpe, eff, loc) =>
      // LOWERING: cast erasure (mkCast decides cast vs. bytecode-verifier crash)
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      mkCast(e, t, subst(eff), loc)

    case TypedAst.Expr.Unsafe(exp, _, _, tpe, eff, loc) =>
      // LOWERING: cast erasure (mkCast decides cast vs. bytecode-verifier crash)
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      mkCast(e, t, subst(eff), loc)


    case TypedAst.Expr.Throw(exp, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Throw, List(e), t, subst(eff), loc)

    case TypedAst.Expr.TryCatch(exp, rules, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      val rs = rules.map(lowerCatchRule(_, env0, subst))
      MonoAst.Expr.TryCatch(e, rs, t, subst(eff), loc)

    case TypedAst.Expr.Handler(symUse, rules, bodyTpe, bodyEff0, handledEff, tpe, loc) =>
      // LOWERING: handler sym { rules }
      // is lowered to
      // handlerBody -> try handlerBody() with sym { rules }
      val bodySym = Symbol.freshVarSym("handlerBody", BoundBy.FormalParam, loc.asSynthetic)(RegionScope.Top, flix)
      val rs = rules.map(lowerHandlerRule(_, env0, subst))
      val bt = visitType(bodyTpe, subst)
      val t = visitType(tpe, subst)
      val bodyEff = subst(bodyEff0)
      val bodyThunkType = Type.mkArrowWithEffect(Type.Unit, bodyEff, bt, loc.asSynthetic)
      val bodyVar = MonoAst.Expr.Var(bodySym, bodyThunkType, loc.asSynthetic)
      val body = MonoAst.Expr.ApplyClo(bodyVar, MonoAst.Expr.Cst(Constant.Unit, Type.Unit, loc.asSynthetic), bt, bodyEff, loc.asSynthetic)
      val RunWith = MonoAst.Expr.RunWith(body, symUse, rs, bt, subst(handledEff), loc)
      val param = MonoAst.FormalParam(bodySym, bodyThunkType, Occur.Unknown, loc.asSynthetic)
      MonoAst.Expr.Lambda(param, RunWith, t, loc)

    case TypedAst.Expr.RunWith(exp1, exp2, tpe, eff, loc) =>
      // LOWERING: run exp1 with exp2
      // is lowered to
      // exp2(_runWith -> exp1)
      val e1 = visitExp(exp1, env0, subst)
      val unitParam = MonoAst.FormalParam(Symbol.freshVarSym("_runWith", BoundBy.FormalParam, loc.asSynthetic)(RegionScope.Top, flix), Type.Unit, Occur.Unknown, loc.asSynthetic)
      val thunkType = Type.mkArrowWithEffect(Type.Unit, e1.eff, e1.tpe, loc.asSynthetic)
      val thunk = MonoAst.Expr.Lambda(unitParam, e1, thunkType, loc.asSynthetic)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyClo(visitExp(exp2, env0, subst), thunk, t, subst(eff), loc)

    case TypedAst.Expr.InvokeConstructor(constructor, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      // LOWERING: box primitive args where Java expects Object (e.g., `new SimpleEntry(42, true)`).
      val javaParamTypes = constructor.getParameterTypes
      val boxedArgs = es.zip(javaParamTypes).map { case (arg, paramType) => boxIfNecessary(arg, paramType) }
      MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeConstructor(constructor), boxedArgs, t, subst(eff), loc)

    case TypedAst.Expr.InvokeSuperConstructor(constructor, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeSuperConstructor(constructor), es, t, subst(eff), loc)

    case TypedAst.Expr.InvokeMethod(method, exp, exps, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      // LOWERING: box primitive args and unbox Object returns for Java generic methods.
      // E.g., `m.put("k", 42)` boxes 42 via Integer.valueOf; `m.get("k")` unboxes via intValue.
      val javaParamTypes = method.getParameterTypes
      val boxedArgs = es.zip(javaParamTypes).map { case (arg, paramType) => boxIfNecessary(arg, paramType) }
      val javaReturnType = method.getReturnType
      val needsUnbox = isPrimType(t) && !javaReturnType.isPrimitive
      val invokeType = if (needsUnbox) boxedWrapperType(t, loc) else t
      val invoke = MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeMethod(method), e :: boxedArgs, invokeType, subst(eff), loc)
      unboxIfNecessary(invoke, t, javaReturnType)

    case TypedAst.Expr.InvokeSuperMethod(method, exps, tpe, eff, loc) =>
      // LOWERING: super call routed through the NewObject this-ref (LocalContext)
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      (lctx.sym, lctx.thisRef) match {
        case (Some(sym), Some(thisRef)) =>
          MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeSuperMethod(sym, method), thisRef :: es, t, subst(eff), loc)
        case _ =>
          throw InternalCompilerException("InvokeSuperMethod outside NewObject context", loc)
      }

    case TypedAst.Expr.InvokeStaticMethod(method, exps, tpe, eff, loc) =>
      val es = exps.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      // LOWERING: box primitive args and unbox Object returns (same as InvokeMethod).
      val javaParamTypes = method.getParameterTypes
      val boxedArgs = es.zip(javaParamTypes).map { case (arg, paramType) => boxIfNecessary(arg, paramType) }
      val javaReturnType = method.getReturnType
      val needsUnbox = isPrimType(t) && !javaReturnType.isPrimitive
      val invokeType = if (needsUnbox) boxedWrapperType(t, loc) else t
      val invoke = MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeStaticMethod(method), boxedArgs, invokeType, subst(eff), loc)
      unboxIfNecessary(invoke, t, javaReturnType)

    case TypedAst.Expr.GetField(field, exp, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.GetField(field), List(e), t, subst(eff), loc)

    case TypedAst.Expr.PutField(field, exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.PutField(field), List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.GetStaticField(field, tpe, eff, loc) =>
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.GetStaticField(field), List.empty, t, subst(eff), loc)

    case TypedAst.Expr.PutStaticField(field, exp, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.PutStaticField(field), List(e), t, subst(eff), loc)

    case TypedAst.Expr.NewObject(sym, clazz, tpe, eff, constructors, methods, loc) =>
      // LOWERING: this-ref LocalContext for anonymous-class methods.
      // NB: the thisRef must use the FRESHENED fparam sym (the method body's vars are renamed),
      // so the fparams are specialized here, before the body is visited under the new lctx.
      // Mint a fresh anonymous class symbol for each specialization. Otherwise distinct
      // specializations of an enclosing generic def (e.g. `mk[String]` and `mk[Int32]`)
      // would reuse the same anonymous class name and collide, so one specialization would
      // run with the other's generated class.
      val freshSym = Symbol.mkFreshAnonClassSym(sym.loc)
      val cs = constructors.map {
        case TypedAst.JvmConstructor(cExp, cRetTpe, cEff, cLoc) =>
          MonoAst.JvmConstructor(visitExp(cExp, env0, subst), visitType(cRetTpe, subst), subst(cEff), cLoc)
      }
      val ms = methods.map {
        case TypedAst.JvmMethod(mAnn, mIdent, mFparams0, mExp, mRetTpe, mEff, mLoc) =>
          val (mFparams, env1) = specializeFormalParams(mFparams0, subst)
          val fs = mFparams.map(lowerFormalParam).map(SolutionSpecialization.rewriteFormalParam)
          val thisParam = fs.head
          val thisRef = MonoAst.Expr.Var(thisParam.sym, thisParam.tpe, loc)
          implicit val lctx: LocalContext = LocalContext(Some(freshSym), Some(thisRef))
          val e0 = visitExp(mExp, env0 ++ env1, subst)
          // If this method overrides a Java method whose erased return type is a reference
          // (e.g. `Object` for a generic interface method) but the Flix result is a primitive,
          // box it so the value matches the erased JVM signature. This mirrors the boxing applied
          // to generic Java method *calls* above (see `boxIfNecessary`), and the call site
          // unboxes the result symmetrically.
          val e = overriddenJavaReturnType(clazz, mIdent.name, fs.tail.length) match {
            case Some(javaReturnType) => boxIfNecessary(e0, javaReturnType)
            case None => e0
          }
          MonoAst.JvmMethod(mAnn, mIdent, fs, e, e.tpe, subst(mEff), mLoc)
      }
      val t = visitType(tpe, subst)
      MonoAst.Expr.NewObject(freshSym, clazz, t, subst(eff), cs, ms, loc)

    case TypedAst.Expr.NewChannel(exp, tpe, eff, loc) =>
      // LOWERING: channel primitive → Concurrent.Channel call
      val e = visitExp(exp, env0, subst)
      lowerNewChannel(e, subst(tpe), subst(eff), loc)

    case TypedAst.Expr.GetChannel(innerExp, tpe, eff, loc) =>
      // LOWERING: channel primitive → Concurrent.Channel call
      // NB: the channel's own RAW substituted type (innerExp.tpe) is threaded in separately from
      // the visited `e` — `e.tpe` is already enum/struct-rewritten (Step 2), which would corrupt
      // mkGetChannel's own def-lookup key if a specialized generic enum flowed through the channel.
      val e = visitExp(innerExp, env0, subst)
      mkGetChannel(e, subst(innerExp.tpe), subst(tpe), subst(eff), loc)

    case TypedAst.Expr.PutChannel(innerExp1, innerExp2, _, eff, loc) =>
      // LOWERING: channel primitive → Concurrent.Channel call
      // NB: same raw-type-threading reasoning as GetChannel above.
      val exp1 = visitExp(innerExp1, env0, subst)
      val exp2 = visitExp(innerExp2, env0, subst)
      SolutionLowering.mkPutChannel(exp1, exp2, subst(innerExp1.tpe), subst(innerExp2.tpe), subst(eff), loc)

    case TypedAst.Expr.SelectChannel(rules0, default0, tpe, eff, loc) =>
      // LOWERING: select → Concurrent.Channel admin/select calls (mkSelectChannel)
      // NB: each rule's RAW substituted channel type is threaded alongside — same reasoning as
      // GetChannel/PutChannel/ParYield above (the visited `chan` expr's own `.tpe` is already
      // enum/struct-rewritten, which would corrupt the synthesized admin/get calls' lookup keys).
      val rules = rules0.map {
        case TypedAst.SelectChannelRule(bnd, chan, exp, _) =>
          val freshSym = Symbol.freshVarSym(bnd.sym)
          val env1 = env0 + (bnd.sym -> freshSym)
          // lowerType (Sender/Receiver -> Mpmc) applied up front: extractChannelTpe expects the
          // already-lowered Mpmc[T, IO] shape, not the raw Receiver[T]/Sender[T] surface type.
          (freshSym, visitExp(chan, env1, subst), visitExp(exp, env1, subst), lowerType(subst(chan.tpe)))
      }
      val default = default0.map(visitExp(_, env0, subst))
      val t = visitType(tpe, subst)
      SolutionLowering.mkSelectChannel(rules, default, t, subst(eff), loc)

    case TypedAst.Expr.Spawn(exp1, exp2, tpe, eff, loc) =>
      val e1 = visitExp(exp1, env0, subst)
      val e2 = visitExp(exp2, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Spawn, List(e1, e2), t, subst(eff), loc)

    case TypedAst.Expr.ParYield(frags, exp, tpe, eff, loc) =>
      // LOWERING: par-yield → channels (mkParYield)
      // NB: each fragment's RAW substituted type is threaded alongside the visited expr — the
      // synthesized channel plumbing needs it for its own def-lookup keys (same reasoning as
      // GetChannel/PutChannel above), since the visited expr's own `.tpe` is already rewritten.
      var curEnv = env0
      val fs = frags.map {
        case TypedAst.ParYieldFragment(pat, fragExp, fragLoc) =>
          val (p, env1) = visitPat(pat, Map.empty, subst)
          curEnv ++= env1
          (p, visitExp(fragExp, curEnv, subst), subst(fragExp.tpe), fragLoc)
      }
      val e = visitExp(exp, curEnv, subst)
      val t = visitType(tpe, subst)
      SolutionLowering.mkParYield(fs, e, t, subst(eff), loc)

    case TypedAst.Expr.Lazy(exp, tpe, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Lazy, List(e), t, Type.Pure, loc)

    case TypedAst.Expr.Force(exp, tpe, eff, loc) =>
      val e = visitExp(exp, env0, subst)
      val t = visitType(tpe, subst)
      MonoAst.Expr.ApplyAtomic(AtomicOp.Force, List(e), t, subst(eff), loc)

    case TypedAst.Expr.FixpointConstraintSet(cs, _, loc) =>
      // LOWERING: Datalog constraint set → Fixpoint.Ast.Datalog value
      lowerConstraintSet(cs, loc, env0, subst)

    case TypedAst.Expr.FixpointLambda(pparams, exp, _, eff, loc) =>
      // LOWERING: predicate rename via the Fixpoint solver's rename function
      val resultType = Types.Datalog
      val defn = lookup(Defs.Rename, resultType)
      val predExps = mkList(pparams.map(pparam => mkPredSym(pparam.pred)), Types.PredSym, loc)
      val argExps = predExps :: visitExp(exp, env0, subst) :: Nil
      MonoAst.Expr.ApplyDef(defn, argExps, Types.RenameType, resultType, subst(eff), loc)

    case TypedAst.Expr.FixpointMerge(exp1, exp2, _, eff, loc) =>
      // LOWERING: Datalog merge → Fixpoint solver merge call
      val resultType = Types.Datalog
      val defn = lookup(Defs.Merge, resultType)
      val argExps = visitExp(exp1, env0, subst) :: visitExp(exp2, env0, subst) :: Nil
      MonoAst.Expr.ApplyDef(defn, argExps, Types.MergeType, resultType, subst(eff), loc)

    case TypedAst.Expr.FixpointQueryWithProvenance(exps, select, withh, tpe0, eff, loc) =>
      // LOWERING: Datalog query → Fixpoint solver provenanceOf call
      lowerQueryWithProvenance(exps, select, withh, subst(tpe0), subst(eff), loc, env0, subst)

    case TypedAst.Expr.FixpointQueryWithSelect(exps, queryExp, selects, _, _, pred, tpe, eff, loc) =>
      // LOWERING: Datalog query → Fixpoint solver solve+facts calls
      lowerQueryWithSelect(exps, queryExp, selects, pred, subst(tpe), subst(eff), loc, env0, subst)

    case TypedAst.Expr.FixpointSolveWithProject(exps, optPreds, mode, _, eff, loc) =>
      // LOWERING: Datalog solve → Fixpoint solver solve+project calls
      lowerSolveWithProject(exps, optPreds, mode, subst(eff), loc, env0, subst)

    case TypedAst.Expr.FixpointInjectInto(exps, predsAndArities, _, _, loc) =>
      // LOWERING: Datalog inject → Fixpoint solver projectInto calls
      lowerInjectInto(exps, predsAndArities, loc, env0, subst)

    case TypedAst.Expr.ApplySig(symUse, exps, _, _, itpe, tpe, eff, _, loc) =>
      // Resolve the sig to its concrete instance def (or default impl), then emit as ApplyDef.
      val it = subst(itpe)
      val resolvedDef = resolveSigSym(symUse.sym, it)(ctx.instances, root, flix)
      val newSym = lookupSym(resolvedDef.sym, it)
      val es = exps.map(visitExp(_, env0, subst))
      MonoAst.Expr.ApplyDef(newSym, es, visitTypeSubstituted(it), visitType(tpe, subst), subst(eff), loc)

    case TypedAst.Expr.Error(m, _, _) =>
      throw InternalCompilerException(s"Unexpected error expression near", m.loc)

  }

  /**
    * Specializes and lowers the given catch rule `rule0` (fresh binder, like every other binder).
    */
  private def lowerCatchRule(rule: TypedAst.CatchRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.CatchRule = rule match {
    case TypedAst.CatchRule(bnd, clazz, exp, _) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      val env1 = env0 + (bnd.sym -> freshSym)
      val e = visitExp(exp, env1, subst)
      MonoAst.CatchRule(freshSym, clazz, e)
  }

  /**
    * Specializes and lowers the given handler rule `rule0` (fresh formal params).
    */
  private def lowerHandlerRule(rule0: TypedAst.HandlerRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.HandlerRule = rule0 match {
    case TypedAst.HandlerRule(opSymUse, fparams0, body0, _) =>
      val (fparams1, env1) = specializeFormalParams(fparams0, subst)
      val fparams = fparams1.map(lowerFormalParam).map(SolutionSpecialization.rewriteFormalParam)
      val body = visitExp(body0, env0 ++ env1, subst)
      MonoAst.HandlerRule(opSymUse, fparams, body)
  }

  /**
    * Specializes and lowers the given match rule `rule0`. The pattern's fresh binders extend the
    * env for both the guard and the body.
    */
  private def visitMatchRule(rule0: TypedAst.MatchRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.MatchRule = rule0 match {
    case TypedAst.MatchRule(pat, guard, body, _) =>
      val (p, env1) = visitPat(pat, Map.empty, subst)
      val extendedEnv = env0 ++ env1
      val g = guard.map(visitExp(_, extendedEnv, subst))
      val b = visitExp(body, extendedEnv, subst)
      MonoAst.MatchRule(p, g, b)
  }

  /**
    * Specializes and lowers the given pattern `pat0`, returning the fresh-binder env extension
    * alongside.
    */
  private def visitPat(pat0: TypedAst.Pattern, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): (MonoAst.Pattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case TypedAst.Pattern.Wild(tpe, loc) =>
      (MonoAst.Pattern.Wild(visitType(tpe, subst), loc), env0)

    case TypedAst.Pattern.Var(bnd, tpe, loc) =>
      val env = if (env0.contains(bnd.sym)) env0 else env0 + (bnd.sym -> Symbol.freshVarSym(bnd.sym))
      (MonoAst.Pattern.Var(env(bnd.sym), visitType(tpe, subst), Occur.Unknown, loc), env)

    case TypedAst.Pattern.Cst(cst, tpe, loc) =>
      (MonoAst.Pattern.Cst(cst, visitType(tpe, subst), loc), env0)

    case TypedAst.Pattern.Tag(symUse, pats, tpe, loc) =>
      val (ps, env) = visitPats(pats, env0, subst)
      // The pattern's own type IS the scrutinee's enum type: the solver-solution lookup key
      // (pre-lowering). Strict: a miss is a Solver gap.
      val t = subst(tpe)
      val newSym = lookupCaseSym(symUse.sym, t)
      (MonoAst.Pattern.Tag(SymUse.CaseSymUse(newSym, symUse.loc), ps, visitTypeSubstituted(t), loc), env)

    case TypedAst.Pattern.Tuple(elms, tpe, loc) =>
      val (ps, env) = visitPats(elms.toList, env0, subst)
      (MonoAst.Pattern.Tuple(Nel(ps.head, ps.tail), visitType(tpe, subst), loc), env)

    case TypedAst.Pattern.Record(pats, pat, tpe, loc) =>
      val (psVal, envs) = pats.map {
        case TypedAst.Pattern.Record.RecordLabelPattern(label, pat1, tpe1, loc1) =>
          val (p1, env1) = visitPat(pat1, env0, subst)
          (MonoAst.Pattern.Record.RecordLabelPattern(label, p1, visitType(tpe1, subst), loc1), env1)
      }.unzip
      val (patVal, env1) = visitPat(pat, env0, subst)
      val env = (env1 :: envs).foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _)
      (MonoAst.Pattern.Record(psVal, patVal, visitType(tpe, subst), loc), env)

    case TypedAst.Pattern.Error(_, loc) =>
      throw InternalCompilerException(s"Unexpected pattern: '$pat0'.", loc)
  }

  /**
    * Specializes and lowers `ps`, threading the env through left-to-right binder freshening.
    */
  private def visitPats(ps: List[TypedAst.Pattern], env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): (List[MonoAst.Pattern], Map[Symbol.VarSym, Symbol.VarSym]) =
    ps.foldRight((Nil: List[MonoAst.Pattern], env0)) {
      case (pat0, (res, env1)) =>
        val (pat, env) = visitPat(pat0, env1, subst)
        (pat :: res, env)
    }

  /**
    * Specializes and lowers the given restrictable choice rule `rule0` to a match rule.
    */
  private def lowerRestrictableChooseRule(rule0: TypedAst.RestrictableChooseRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.MatchRule = rule0 match {
    case TypedAst.RestrictableChooseRule(pat, exp) =>
      pat match {
        case TypedAst.RestrictableChoosePattern.Tag(symUse, pat0, tpe, loc) =>
          val env = pat0.foldLeft(env0) {
            case (env1, TypedAst.RestrictableChoosePattern.Var(bnd, _, _)) =>
              env1 + (bnd.sym -> Symbol.freshVarSym(bnd.sym))
            case (env1, TypedAst.RestrictableChoosePattern.Wild(_, _)) => env1
            case (_, TypedAst.RestrictableChoosePattern.Error(_, errLoc)) => throw InternalCompilerException("unexpected restrictable choose variable", errLoc)
          }
          val termPatterns = pat0.map {
            case TypedAst.RestrictableChoosePattern.Var(TypedAst.Binder(varSym, _), varTpe, varLoc) => MonoAst.Pattern.Var(env(varSym), subst(varTpe), Occur.Unknown, varLoc)
            case TypedAst.RestrictableChoosePattern.Wild(wildTpe, wildLoc) => MonoAst.Pattern.Wild(subst(wildTpe), wildLoc)
            case TypedAst.RestrictableChoosePattern.Error(_, errLoc) => throw InternalCompilerException("unexpected restrictable choose variable", errLoc)
          }
          val tagSymUse = lowerRestrictableCaseSymUse(symUse)
          val p = MonoAst.Pattern.Tag(tagSymUse, termPatterns, visitType(tpe, subst), loc)
          MonoAst.MatchRule(p, None, visitExp(exp, env, subst))
        case TypedAst.RestrictableChoosePattern.Error(_, loc) => throw InternalCompilerException("unexpected error restrictable choose pattern", loc)
      }
  }

  /**
    * Lowers `sym` from a restrictable case sym use into a regular case sym use.
    */
  private def lowerRestrictableCaseSymUse(symUse: SymUse.RestrictableCaseSymUse): SymUse.CaseSymUse = {
    SymUse.CaseSymUse(lowerRestrictableCaseSym(symUse.sym), symUse.sym.loc)
  }

  private def visitExtPat(pat0: TypedAst.ExtPattern, subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): (MonoAst.ExtPattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case TypedAst.ExtPattern.Default(loc) =>
      (MonoAst.ExtPattern.Default(loc), Map.empty)

    case TypedAst.ExtPattern.Tag(label, pats, loc) =>
      val (ps, symMaps) = pats.map(visitExtTagPat(_, subst)).unzip
      (MonoAst.ExtPattern.Tag(label, ps, loc), symMaps.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _))

    case TypedAst.ExtPattern.Error(loc) =>
      throw InternalCompilerException("unexpected error ext pattern", loc)
  }

  private def visitExtTagPat(pat0: TypedAst.ExtTagPattern, subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): (MonoAst.ExtTagPattern, Map[Symbol.VarSym, Symbol.VarSym]) = pat0 match {
    case TypedAst.ExtTagPattern.Wild(tpe, loc) =>
      (MonoAst.ExtTagPattern.Wild(visitType(tpe, subst), loc), Map.empty)

    case TypedAst.ExtTagPattern.Var(bnd, tpe, loc) =>
      val freshSym = Symbol.freshVarSym(bnd.sym)
      (MonoAst.ExtTagPattern.Var(freshSym, visitType(tpe, subst), Occur.Unknown, loc), Map(bnd.sym -> freshSym))

    case TypedAst.ExtTagPattern.Unit(tpe, loc) =>
      (MonoAst.ExtTagPattern.Unit(visitType(tpe, subst), loc), Map.empty)

    case TypedAst.ExtTagPattern.Error(_, loc) =>
      throw InternalCompilerException("unexpected error ext pattern", loc)
  }

  private def lowerExtMatch(rule0: TypedAst.ExtMatchRule, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.ExtMatchRule = rule0 match {
    case TypedAst.ExtMatchRule(pat, exp, loc) =>
      val (p, env1) = visitExtPat(pat, subst)
      val e = visitExp(exp, env0 ++ env1, subst)
      MonoAst.ExtMatchRule(p, e, loc)
  }

  private def lowerFormalParam(fparam: TypedAst.FormalParam): MonoAst.FormalParam = fparam match {
    case TypedAst.FormalParam(bnd, tpe, _, _, loc0) => MonoAst.FormalParam(bnd.sym, lowerType(tpe), Occur.Unknown, loc0)
  }

  private def lowerTypeParam(tparam: TypedAst.TypeParam): MonoAst.TypeParam = tparam match {
    case TypedAst.TypeParam(name, sym, loc) =>
      MonoAst.TypeParam(name, sym, loc)
  }

  /**
    * Wraps an entry point function with calls to the default handlers of each of the effects appearing in
    * its signature. The order in which the handlers are applied is not defined and should not be relied upon.
    *
    * For example, if we had default handlers for some effects A, B and C:
    *
    * Transforms a function:
    * {{{
    *     def f(arg1: tpe1, ...): tpe \ A + B = exp
    * }}}
    * Into:
    * {{{
    *     def f(arg1: tpe1, ...): tpe \ (((ef - A) + IO) - B) + IO =
    *         handlerB(_ -> handlerA(_ ->exp))
    * }}}
    *
    * Each of the wrappers:
    *   - Removes the handled effect from the function's effect set and adds IO
    *   - Creates a lambda (_ -> originalBody) and passes it to each handler
    *   - Updates the function's type signature accordingly
    *
    * @param currentDef The entry point function definition to wrap
    * @param root       The typed AST root
    * @return The wrapped function definition with all necessary default effect handlers
    */
  // ---- LOWERING: entry-point default-handler wrapping --------------------------------------
  private def wrapDefWithDefaultHandlers(currentDef: TypedAst.Def)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Def = {
    // Obtain the concrete effect set of the definition that is going to be wrapped.
    // We are expecting entry points, and all entry points should have a concrete effect set.
    val defEffects: CofiniteSet[Symbol.EffSym] = Type.eval(currentDef.spec.eff) match {
      case Result.Ok(s) => s
      // This means eff is either not well-formed or it has type variables.
      // Either way, in this case we will wrap with all default handlers
      // to make sure that the effects present in the signature that have default handlers are handled
      case Result.Err(_) => throw InternalCompilerException("Unexpected illegal effect set on entry point", currentDef.spec.eff.loc)
    }
    // Gather only the default handlers for the effects appearing in the signature of the definition.
    val requiredHandlers = root.defaultHandlers.filter(h => defEffects.contains(h.handledSym))
    // Wrap the expression in each of the required default handlers.
    // Right now, the order depends on the order of defaultHandlers.
    requiredHandlers.foldLeft(currentDef)((defn, handler) => wrapInHandler(defn, handler))
  }

  /**
    * Wraps an entry point function with a default effect handler.
    *
    * Transforms a function:
    * {{{
    *     def f(arg1: tpe1, ...): tpe \ ef = exp
    * }}}
    *
    * Into:
    * {{{
    *     def f(arg1: tpe1, ...): tpe \ (ef - handledEffect) + IO =
    *         handler(_ -> exp)
    * }}}
    *
    * The wrapper:
    *   - Removes the handled effect from the function's effect set and adds IO
    *   - Creates a lambda (_ -> originalBody) and passes it to each handler
    *   - Updates the function's type signature accordingly
    *
    * @param defn           The entry point function definition to wrap
    * @param defaultHandler Information about the default handler to apply
    * @return The wrapped function definition with updated effect signature
    */
  private def wrapInHandler(defn: TypedAst.Def, defaultHandler: DefaultHandler)(implicit flix: Flix): TypedAst.Def = {
    // Create synthetic locations
    val effLoc = defn.spec.eff.loc.asSynthetic
    val baseTypeLoc = defn.spec.declaredScheme.base.loc.asSynthetic
    val expLoc = defn.exp.loc.asSynthetic
    // The new type is the same as the wrapped def with an effect set of
    // `(ef - handledEffect) + IO` where `ef` is the effect set of the previous definition.
    val effDif = Type.mkDifference(defn.spec.eff, defaultHandler.handledEff, effLoc)
    // Technically we could perform this outside at the wrapInHandlers level
    // by just checking the length of the handlers and if it is greater than 0
    // just adding IO. However, that would only work while default handlers can only generate IO.
    // Canonicalized (not left as a raw `(ef - handledEff) + IO` formula): the solution-driven
    // specializer's defTable keys are built via StrictSubstitution, which canonicalizes ground
    // effect formulas on the way in (see MonomorphCanon). The synthesized ApplyDef's `itpe`
    // (handlerArrowType below) must be in that same canonical form, or the (sym, type) lookup
    // that visitExp performs when it later visits this node misses even though the types are
    // semantically equal.
    val eff = MonomorphCanon.canonicalEffect(Type.mkUnion(effDif, Type.IO, effLoc))
    val tpe = Type.mkCurriedArrowWithEffect(defn.spec.fparams.map(_.tpe), eff, defn.spec.retTpe, baseTypeLoc)
    val spec = defn.spec.copy(
      declaredScheme = defn.spec.declaredScheme.copy(base = tpe),
      eff = eff,
    )
    // Create _ -> exp
    val innerLambda =
      TypedAst.Expr.Lambda(
        TypedAst.FormalParam(
          TypedAst.Binder(Symbol.freshVarSym("_", BoundBy.FormalParam, expLoc)(RegionScope.Top, flix), Type.Unit),
          Type.Unit,
          TypeSource.Inferred,
          Decreasing.NonDecreasing,
          expLoc
        ),
        defn.exp,
        Type.mkArrowWithEffect(Type.Unit, defn.spec.eff, defn.spec.retTpe, expLoc),
        expLoc
      )
    // Create the instantiated type of the handler
    val handlerArrowType = Type.mkArrowWithEffect(innerLambda.tpe, eff, defn.spec.retTpe, expLoc)
    // Create HandledEff.handle(_ -> exp)
    // The handler sym is embedded unresolved: this synthesized TypedAst node is subsequently
    // visited by visitExp, whose ApplyDef case resolves it against the solver solution like any
    // other call site. Resolving it here instead would make visitExp re-look-up an already-fresh
    // sym, which is not in allDefs and crashes.
    val handlerDefSymUse = SymUse.DefSymUse(defaultHandler.handlerSym, expLoc)
    val handlerCall = TypedAst.Expr.ApplyDef(handlerDefSymUse, List(innerLambda), List(innerLambda.tpe), handlerArrowType, defn.spec.retTpe, eff, ApplyPosition.NonTail, expLoc)
    defn.copy(spec = spec, exp = handlerCall)
  }

  /**
    * Lowers `sym` from a restrictable enum sym into a regular enum sym.
    */
  private def lowerRestrictableEnumSym(sym: Symbol.RestrictableEnumSym): Symbol.EnumSym =
    new Symbol.EnumSym(None, sym.namespace, sym.name, sym.loc)

  /**
    * Returns the definition associated with the given symbol `sym`.
    *
    * @param tpe must be specialized. Can be visited, if the underlying function can handle that
    */
  private def lookup(sym: Symbol.DefnSym, tpe: Type)(implicit ctx: Context): Symbol.DefnSym =
    lookupSym(sym, tpe)

  /**
    * Returns the cast of `e` to `tpe` and `eff`.
    *
    * If `exp` and `tpe` is bytecode incompatible, a runtime crash is inserted to appease the
    * bytecode verifier.
    */
  private def mkCast(exp: MonoAst.Expr, tpe: Type, eff: Type, loc: SourceLocation): MonoAst.Expr = {
    (exp.tpe, tpe) match {
      case (Type.Char, Type.Char) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Char, Type.Int16) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Int16, Type.Char) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Bool, Type.Bool) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Int8, Type.Int8) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Int16, Type.Int16) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Int32, Type.Int32) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Int64, Type.Int64) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Float32, Type.Float32) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (Type.Float64, Type.Float64) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (x, y) if !isPrimType(x) && !isPrimType(y) => MonoAst.Expr.Cast(exp, tpe, eff, loc)
      case (x, y) =>
        val crash = MonoAst.Expr.ApplyAtomic(AtomicOp.CastError(erasedString(x), erasedString(y)), Nil, tpe, eff, loc)
        MonoAst.Expr.Stm(List(exp), crash, tpe, eff, loc)
    }
  }

  /**
    * Returns `true` if `tpe` is a primitive type.
    *
    * N.B.: `tpe` must be normalized.
    */
  private def isPrimType(tpe: Type): Boolean = tpe match {
    case Type.Char => true
    case Type.Bool => true
    case Type.Int8 => true
    case Type.Int16 => true
    case Type.Int32 => true
    case Type.Int64 => true
    case Type.Float32 => true
    case Type.Float64 => true
    case Type.Cst(_, _) => false
    case Type.Apply(_, _, _) => false
    case Type.Var(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.Alias(_, _, _, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.AssocType(_, _, _, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.JvmToType(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.JvmToEff(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.UnresolvedJvmType(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
  }

  /**
    * Returns the erased string representation of `tpe`
    *
    * N.B.: `tpe` must be normalized.
    */
  private def erasedString(tpe: Type): String = tpe match {
    case Type.Char => "Char"
    case Type.Bool => "Bool"
    case Type.Int8 => "Int8"
    case Type.Int16 => "Int16"
    case Type.Int32 => "Int32"
    case Type.Int64 => "Int64"
    case Type.Float32 => "Float32"
    case Type.Float64 => "Float64"
    case Type.Cst(_, _) => "Object"
    case Type.Apply(_, _, _) => "Object"
    case Type.Var(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.Alias(_, _, _, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.AssocType(_, _, _, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.JvmToType(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.JvmToEff(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
    case Type.UnresolvedJvmType(_, _) => throw InternalCompilerException(s"Unexpected type '$tpe'", tpe.loc)
  }

  /**
    * Returns the `JvmType`/`JvmValue` case name for the primitive base type `tpe`, or `"JvmObject"`
    * for anything else.
    */
  private def jvmTypeCaseName(tpe: Type): String = tpe match {
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

  /**
    * Returns the `valueOf` boxing method for a Flix primitive type.
    * This is the same mechanism javac uses to implement autoboxing.
    */
  // ---- LOWERING: Java boxing/unboxing helpers -----------------------------------------------
  private def javaBoxMethod(tpe: Type): java.lang.reflect.Method = tpe match {
    case Type.Bool => classOf[java.lang.Boolean].getMethod("valueOf", java.lang.Boolean.TYPE)
    case Type.Char => classOf[java.lang.Character].getMethod("valueOf", java.lang.Character.TYPE)
    case Type.Int8 => classOf[java.lang.Byte].getMethod("valueOf", java.lang.Byte.TYPE)
    case Type.Int16 => classOf[java.lang.Short].getMethod("valueOf", java.lang.Short.TYPE)
    case Type.Int32 => classOf[java.lang.Integer].getMethod("valueOf", java.lang.Integer.TYPE)
    case Type.Int64 => classOf[java.lang.Long].getMethod("valueOf", java.lang.Long.TYPE)
    case Type.Float32 => classOf[java.lang.Float].getMethod("valueOf", java.lang.Float.TYPE)
    case Type.Float64 => classOf[java.lang.Double].getMethod("valueOf", java.lang.Double.TYPE)
    case _ => throw InternalCompilerException(s"Unexpected non-primitive type '$tpe'", tpe.loc)
  }

  /**
    * Returns the unboxing method (e.g., `intValue`) for a Flix primitive type.
    * This is the same mechanism javac uses to implement auto-unboxing.
    */
  private def javaUnboxMethod(tpe: Type): java.lang.reflect.Method = tpe match {
    case Type.Bool => classOf[java.lang.Boolean].getMethod("booleanValue")
    case Type.Char => classOf[java.lang.Character].getMethod("charValue")
    case Type.Int8 => classOf[java.lang.Byte].getMethod("byteValue")
    case Type.Int16 => classOf[java.lang.Short].getMethod("shortValue")
    case Type.Int32 => classOf[java.lang.Integer].getMethod("intValue")
    case Type.Int64 => classOf[java.lang.Long].getMethod("longValue")
    case Type.Float32 => classOf[java.lang.Float].getMethod("floatValue")
    case Type.Float64 => classOf[java.lang.Double].getMethod("doubleValue")
    case _ => throw InternalCompilerException(s"Unexpected non-primitive type '$tpe'", tpe.loc)
  }

  /**
    * Returns the Flix Type for the Java wrapper class of a primitive type.
    * E.g., `Bool` -> `Native(java.lang.Boolean)`, `Int32` -> `Native(java.lang.Integer)`.
    */
  private def boxedWrapperType(tpe: Type, loc: SourceLocation): Type = tpe match {
    case Type.Bool => Type.Cst(TypeConstructor.Native(classOf[java.lang.Boolean]), loc)
    case Type.Char => Type.Cst(TypeConstructor.Native(classOf[java.lang.Character]), loc)
    case Type.Int8 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Byte]), loc)
    case Type.Int16 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Short]), loc)
    case Type.Int32 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Integer]), loc)
    case Type.Int64 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Long]), loc)
    case Type.Float32 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Float]), loc)
    case Type.Float64 => Type.Cst(TypeConstructor.Native(classOf[java.lang.Double]), loc)
    case _ => throw InternalCompilerException(s"Unexpected non-primitive type '$tpe'", tpe.loc)
  }

  /**
    * Boxes `arg` if the actual arg type (Flix primitive) mismatches the expected param type (Object).
    * E.g., in `m.put("k", 42)` on a `HashMap[String, Int32]`, the actual type is `Int32`
    * but the expected type is `Object` (erased), so `42` is boxed via `Integer.valueOf(42)`.
    */
  private def boxIfNecessary(arg: MonoAst.Expr, expectedParamType: Class[?]): MonoAst.Expr = {
    val actualArgType = arg.tpe
    if (isPrimType(actualArgType) && !expectedParamType.isPrimitive) {
      MonoAst.Expr.ApplyAtomic(
        AtomicOp.InvokeStaticMethod(javaBoxMethod(actualArgType)),
        List(arg),
        boxedWrapperType(actualArgType, arg.loc),
        arg.eff,
        arg.loc.asSynthetic
      )
    } else arg
  }

  /** Returns the erased return type of the Java method on `clazz` matching `name` and `arity` (excluding the receiver). */
  private def overriddenJavaReturnType(clazz: Class[?], name: String, arity: Int): Option[Class[?]] =
    JvmUtils.getOverridableInstanceMethods(clazz).collectFirst {
      case m if m.getName == name && m.getParameterCount == arity => m.getReturnType
    }

  /**
    * Unboxes `expr` if the expected return type (Flix primitive) mismatches the actual return type (Object).
    * E.g., in `let v: Int32 = m.get("k")` on a `HashMap[String, Int32]`, the expected type is
    * `Int32` but the actual Java return type is `Object` (erased), so the result is unboxed via `intValue()`.
    */
  private def unboxIfNecessary(expr: MonoAst.Expr, expectedReturnType: Type, actualReturnType: Class[?]): MonoAst.Expr = {
    if (isPrimType(expectedReturnType) && !actualReturnType.isPrimitive) {
      MonoAst.Expr.ApplyAtomic(
        AtomicOp.InvokeMethod(javaUnboxMethod(expectedReturnType)),
        List(expr),
        expectedReturnType,
        expr.eff,
        expr.loc.asSynthetic
      )
    } else expr
  }

  /**
    * Strips an auto-unboxing wrapper (e.g., `intValue()`) from `expr` if present.
    */
  private def stripAutoUnbox(expr: MonoAst.Expr): MonoAst.Expr = expr match {
    case MonoAst.Expr.ApplyAtomic(AtomicOp.InvokeMethod(method), List(inner), _, _, _)
      if isAutoUnboxMethod(method) => inner
    case _ => expr
  }

  /** Returns `true` if `method` is a Java auto-unboxing method (e.g., `intValue`, `booleanValue`). */
  private def isAutoUnboxMethod(method: java.lang.reflect.Method): Boolean = {
    method.getParameterCount == 0 && (method.getName match {
      case "booleanValue" | "charValue" | "byteValue" | "shortValue" |
           "intValue" | "longValue" | "floatValue" | "doubleValue" => true
      case _ => false
    })
  }

  /**
    * Lowers `sym` from a restrictable case sym into a regular case sym.
    *
    * NB: Ordinal is -1 because restrictable enums do not have fixed ordinals.
    */
  private def lowerRestrictableCaseSym(sym: Symbol.RestrictableCaseSym): Symbol.CaseSym = {
    val enumSym = lowerRestrictableEnumSym(sym.enumSym)
    new Symbol.CaseSym(enumSym, sym.name, -1, sym.loc)
  }

  /**
    * Make a new channel tuple (sender, receiver) expression
    *
    * New channel expressions are rewritten as follows:
    * {{{ %%CHANNEL_NEW%%(m) }}}
    * becomes a call to the standard library function:
    * {{{ Concurrent/Channel.newChannel(10) }}}
    *
    * @param tpe The specialized type of the result
    */
  // ---- LOWERING: channel synthesis helpers --------------------------------------------------
  private def lowerNewChannel(exp: MonoAst.Expr, tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    // itpe is the def-lookup key: computed and used raw (un-rewritten), matching every other
    // lookup-key position in the fused walk — only the node's own field positions get rewritten.
    val itpe = lowerType(Type.mkIoArrow(exp.tpe, tpe, loc))
    val defnSym = lookup(Defs.ChannelNewTuple, itpe)
    MonoAst.Expr.ApplyDef(defnSym, exp :: Nil, SolutionSpecialization.rewriteEnumStructType(itpe), visitTypeSubstituted(tpe), eff, loc)
  }

  /**
    * Make a channel get expression
    *
    * Channel get expressions are rewritten as follows:
    * {{{ <- c }}}
    * becomes a call to the standard library function:
    * {{{ Concurrent/Channel.get(c) }}}
    */
  private def mkGetChannel(exp: MonoAst.Expr, chanTpe: Type, tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    // itpe is the def-lookup key: built from `chanTpe`, the caller's RAW (un-rewritten) substituted
    // channel type — NOT `exp.tpe`, which is already enum/struct-rewritten by the time `exp` (the
    // already-visited channel expression) reaches here. Only the node's own field positions below
    // get the rewrite.
    val itpe = lowerType(Type.mkIoArrow(chanTpe, tpe, loc))
    val defnSym = lookup(Defs.ChannelGet, itpe)
    MonoAst.Expr.ApplyDef(defnSym, exp :: Nil, SolutionSpecialization.rewriteEnumStructType(itpe), visitTypeSubstituted(tpe), eff, loc)
  }

  /**
    * Make a channel put expression
    *
    * Channel put expressions are rewritten as follows:
    * {{{ c <- 42 }}}
    * becomes a call to the standard library function:
    * {{{ let chan = c; let value = 42; Concurrent/Channel.put(value, chan) }}}
    *
    * Here `exp1` is the channel and `exp2` is the value (i.e. `exp1 <- exp2`). In source order
    * the channel is evaluated before the value, but `Channel.put` takes the value before the
    * channel. We let-bind both expressions in source order so that reordering them into the
    * argument list does not change their evaluation order. See:
    * https://github.com/flix/flix/issues/10378
    */
  private def mkPutChannel(exp1: MonoAst.Expr, exp2: MonoAst.Expr, chanTpe: Type, valTpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context, flix: Flix): MonoAst.Expr = {
    // itpe is the def-lookup key: built from the caller's RAW (un-rewritten) substituted
    // chanTpe/valTpe — see mkGetChannel's doc comment for why `exp1.tpe`/`exp2.tpe` can't be used
    // directly (already enum/struct-rewritten by the time the visited exprs reach here).
    val itpe = lowerType(Type.mkIoUncurriedArrow(List(valTpe, chanTpe), Type.Unit, loc))
    val defnSym = lookup(Defs.ChannelPut, itpe)
    val chanSym = mkLetSym("chan", loc)
    val valueSym = mkLetSym("value", loc)
    val chanVar = MonoAst.Expr.Var(chanSym, exp1.tpe, loc)
    val valueVar = MonoAst.Expr.Var(valueSym, exp2.tpe, loc)
    val putExp = MonoAst.Expr.ApplyDef(defnSym, List(valueVar, chanVar), SolutionSpecialization.rewriteEnumStructType(itpe), Type.Unit, eff, loc)
    // The channel binding is the outermost let, so the channel is evaluated before the value.
    val valueLet = MonoAst.Expr.Let(valueSym, exp2, putExp, Type.Unit, eff, Occur.Unknown, loc)
    MonoAst.Expr.Let(chanSym, exp1, valueLet, Type.Unit, eff, Occur.Unknown, loc)
  }

  /**
    * Make a channel select expression
    *
    * Channel select expressions are rewritten as follows:
    * {{{
    *  select {
    *    case x <- ?ch1 => ?handlech1
    *    case y <- ?ch2 => ?handlech2
    *    case _ => ?default
    *  }
    * }}}
    * becomes
    * {{{
    *   let ch1 = ?ch1;
    *   let ch2 = ?ch2;
    *   match selectFrom(mpmcAdmin(ch1) :: mpmcAdmin(ch2) :: Nil, false) {  // true if no default
    *     case (0, locks) =>
    *       let x = unsafeGetAndUnlock(ch1, locks);
    *       ?handlech1
    *     case (1, locks) =>
    *       let y = unsafeGetAndUnlock(ch2, locks);
    *       ?handlech2
    *     case (-1, _) =>                                                  // Omitted if no default
    *      ?default                                                   // Unlock is handled by selectFrom
    * }}}
    * Note: match is not exhaustive: we're relying on the simplifier to handle this for us
    */
  private def mkSelectChannel(rules: List[(Symbol.VarSym, MonoAst.Expr, MonoAst.Expr, Type)], default: Option[MonoAst.Expr], tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val t = lowerType(tpe)

    val channels = rules.map { case (_, c, _, _) => (mkLetSym("chan", loc), c) }
    val admins = mkChannelAdminList(rules, channels, loc)
    val selectExp = mkChannelSelect(admins, default, loc)
    val cases = mkChannelCases(rules, channels, eff, loc)
    val defaultCase = mkSelectDefaultCase(default, loc)
    val matchExp = MonoAst.Expr.Match(selectExp, cases ++ defaultCase, t, eff, loc)

    channels.foldRight[MonoAst.Expr](matchExp) {
      case ((sym, c), e) => MonoAst.Expr.Let(sym, c, e, t, eff, Occur.Unknown, loc)
    }
  }

  /**
    * Make the list of MpmcAdmin objects which will be passed to `selectFrom`.
    *
    * For each case like
    * {{{ x <- ?ch1 => ?handlech1 }}}
    * we generate
    * {{{ mpmcAdmin(x) }}}
    */
  private def mkChannelAdminList(rs: List[(Symbol.VarSym, MonoAst.Expr, MonoAst.Expr, Type)], channels: List[(Symbol.VarSym, MonoAst.Expr)], loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val admins = ListOps.zip(rs, channels) map {
      case ((_, _, _, rawChanTpe), (chanSym, _)) =>
        // itpe/lookup key built from the RAW channel type — see SelectChannel case's doc comment.
        val itpe = lowerType(Type.mkPureArrow(rawChanTpe, Types.ChannelMpmcAdmin, loc))
        val defnSym = lookup(Defs.ChannelMpmcAdmin, itpe)
        MonoAst.Expr.ApplyDef(defnSym, List(MonoAst.Expr.Var(chanSym, visitTypeSubstituted(rawChanTpe), loc)), SolutionSpecialization.rewriteEnumStructType(itpe), Types.ChannelMpmcAdmin, Type.Pure, loc)
    }
    mkList(admins, Types.ChannelMpmcAdmin, loc)
  }

  /**
    * Construct a call to `selectFrom` given a list of MpmcAdmin objects and optional default.
    *
    * Transforms
    * {{{ mpmcAdmin(ch1), mpmcAdmin(ch1), ... }}}
    * Into
    * {{{ selectFrom(mpmcAdmin(ch1) :: mpmcAdmin(ch2) :: ... :: Nil, false) }}}
    *
    * When `default` is `Some` the second parameter will be `true`.
    */
  private def mkChannelSelect(admins: MonoAst.Expr, default: Option[MonoAst.Expr], loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    val locksType = Types.mkList(Types.ConcurrentReentrantLock, loc)

    val selectRetTpe = Type.mkTuple(List(Type.Int32, locksType), loc)
    val itpe = Type.mkIoUncurriedArrow(List(admins.tpe, Type.Bool), selectRetTpe, loc)
    val blocking = default match {
      case Some(_) => MonoAst.Expr.Cst(Constant.Bool(false), Type.Bool, loc)
      case None => MonoAst.Expr.Cst(Constant.Bool(true), Type.Bool, loc)
    }
    val defnSym = lookup(Defs.ChannelSelectFrom, itpe)
    MonoAst.Expr.ApplyDef(defnSym, List(admins, blocking), SolutionSpecialization.rewriteEnumStructType(lowerType(itpe)), SolutionSpecialization.rewriteEnumStructType(selectRetTpe), Type.IO, loc)
  }

  /**
    * Construct a sequence of MatchRules corresponding to the given SelectChannelRules
    *
    * Transforms the `i`'th
    * {{{ case x <- ?ch1 => ?handlech1 }}}
    * into
    * {{{
    * case (i, locks) =>
    *   let x = unsafeGetAndUnlock(ch1, locks);
    *   ?handlech1
    * }}}
    */
  private def mkChannelCases(rs: List[(Symbol.VarSym, MonoAst.Expr, MonoAst.Expr, Type)], channels: List[(Symbol.VarSym, MonoAst.Expr)], eff: Type, loc: SourceLocation)(implicit ctx: Context, flix: Flix): List[MonoAst.MatchRule] = {
    // RAW (lookup-key form) and rewritten (node-field form) both needed — see doc comment above.
    val locksTypeRaw = Types.mkList(Types.ConcurrentReentrantLock, loc)
    val locksType = SolutionSpecialization.rewriteEnumStructType(locksTypeRaw)

    ListOps.zip(rs, channels).zipWithIndex map {
      case (((sym, _, exp, rawChanTpe), (chSym, _)), i) =>
        val locksSym = mkLetSym("locks", loc)
        val pat = mkTuplePattern(Nel(MonoAst.Pattern.Cst(Constant.Int32(i), Type.Int32, loc), List(MonoAst.Pattern.Var(locksSym, locksType, Occur.Unknown, loc))), loc)
        // getTpe/itpe/lookup key built from the RAW channel type — see SelectChannel's doc comment.
        val getTpe = extractChannelTpe(rawChanTpe)
        val itpe = lowerType(Type.mkIoUncurriedArrow(List(rawChanTpe, locksTypeRaw), getTpe, loc))
        val args = List(MonoAst.Expr.Var(chSym, visitTypeSubstituted(rawChanTpe), loc), MonoAst.Expr.Var(locksSym, locksType, loc))
        val defnSym = lookup(Defs.ChannelUnsafeGetAndUnlock, itpe)
        val getExp = MonoAst.Expr.ApplyDef(defnSym, args, SolutionSpecialization.rewriteEnumStructType(itpe), visitTypeSubstituted(getTpe), eff, loc)
        val e = MonoAst.Expr.Let(sym, getExp, exp, exp.tpe, eff, Occur.Unknown, loc)
        MonoAst.MatchRule(pat, None, e)
    }
  }

  /**
    * Construct additional MatchRule to handle the (optional) default case
    * NB: Does not need to unlock because that is handled inside Concurrent/Channel.selectFrom.
    *
    * If `default` is `None` returns an empty list. Otherwise produces
    * {{{ case (-1, _) => ?default }}}
    */
  private def mkSelectDefaultCase(default: Option[MonoAst.Expr], loc: SourceLocation)(implicit ctx: Context): List[MonoAst.MatchRule] = {
    default match {
      case Some(defaultExp) =>
        val locksType = SolutionSpecialization.rewriteEnumStructType(Types.mkList(Types.ConcurrentReentrantLock, loc))
        val pat = mkTuplePattern(Nel(MonoAst.Pattern.Cst(Constant.Int32(-1), Type.Int32, loc), List(MonoAst.Pattern.Wild(locksType, loc))), loc)
        val defaultMatch = MonoAst.MatchRule(pat, None, defaultExp)
        List(defaultMatch)
      case _ =>
        List()
    }
  }

  /**
    * Returns a desugared [[TypedAst.Expr.ParYield]] expression as a nested match-expression.
    */
  private def mkParYield(frags: List[(MonoAst.Pattern, MonoAst.Expr, Type, SourceLocation)], exp: MonoAst.Expr, tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context, flix: Flix): MonoAst.Expr = {
    // Only generate channels for n-1 fragments. We use the current thread for the last fragment.
    val fs = frags.init
    val last = frags.last

    // Generate symbols for each channel.
    val chanSymsWithPatAndExp = fs.map { case (p, e, rawTpe, l) => (p, mkLetSym("channel", l.asSynthetic), e, rawTpe) }

    // Make `GetChannel` exps for the spawnable exps.
    val waitExps = mkBoundParWaits(chanSymsWithPatAndExp, exp)

    // Evaluate the last expression in the current thread (so just make let-binding)
    val desugaredYieldExp = mkLetMatch(last._1, last._2, waitExps)

    // Generate channels and spawn exps.
    val chanSymsWithExp = chanSymsWithPatAndExp.map { case (_, s, e, rawTpe) => (s, e, rawTpe) }
    val blockExp = mkParChannels(desugaredYieldExp, chanSymsWithExp)

    // Wrap everything in a purity cast,
    MonoAst.Expr.Cast(blockExp, lowerType(tpe), eff, loc.asSynthetic)
  }

  /**
    * Returns a full `par yield` expression.
    *
    * @param chanSymsWithExps each fragment's channel sym, visited value expr, and the fragment's
    *                         RAW substituted type (needed for mkPutChannel/mkNewChannel's own
    *                         def-lookup keys — see mkGetChannel's doc comment for why `e.tpe`
    *                         alone, already enum/struct-rewritten, isn't safe to reuse here).
    */
  private def mkParChannels(exp: MonoAst.Expr, chanSymsWithExps: List[(Symbol.VarSym, MonoAst.Expr, Type)])(implicit ctx: Context, flix: Flix): MonoAst.Expr = {
    // Make spawn expressions `spawn ch <- exp`.
    val spawns = chanSymsWithExps.foldRight(exp: MonoAst.Expr) {
      case ((sym, e, rawTpe), acc) =>
        val loc = e.loc.asSynthetic
        val e1 = mkChannelExp(sym, rawTpe, loc) // The channel `ch`
        val e2 = mkPutChannel(e1, e, mkChannelTpe(rawTpe, loc), rawTpe, Type.IO, loc) // The put exp: `ch <- exp0`.
        val e3 = MonoAst.Expr.Cst(Constant.Static, Type.mkRegionToStar(Type.IO, loc), loc)
        val e4 = MonoAst.Expr.ApplyAtomic(AtomicOp.Spawn, List(e2, e3), Type.Unit, Type.IO, loc) // Spawn the put expression from above i.e. `spawn ch <- exp0`.
        MonoAst.Expr.Stm(List(e4), acc, acc.tpe, Type.mkUnion(e4.eff, acc.eff, loc), loc) // Return a statement expression containing the other spawn expressions along with this one.
    }

    // Make let bindings `let ch = chan 1;`.
    chanSymsWithExps.foldRight(spawns: MonoAst.Expr) {
      case ((sym, e, rawTpe), acc) =>
        val loc = e.loc.asSynthetic
        val chan = mkNewChannel(MonoAst.Expr.Cst(Constant.Int32(1), Type.Int32, loc), mkChannelTpe(rawTpe, loc), Type.IO, loc) // The channel exp `chan 1`
        MonoAst.Expr.Let(sym, chan, acc, acc.tpe, Type.mkUnion(e.eff, acc.eff, loc), Occur.Unknown, loc) // The let-binding `let ch = chan 1`
    }
  }

  /**
    * Make a new channel expression
    */
  private def mkNewChannel(exp: MonoAst.Expr, tpe: Type, eff: Type, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    val itpe = lowerType(Type.mkIoArrow(exp.tpe, tpe, loc))
    val defnSym = lookup(Defs.ChannelNew, itpe)
    MonoAst.Expr.ApplyDef(defnSym, exp :: Nil, SolutionSpecialization.rewriteEnumStructType(itpe), SolutionSpecialization.rewriteEnumStructType(tpe), eff, loc)
  }

  /**
    * Returns an expression where the pattern variables used in `exp` are
    * bound to [[TypedAst.Expr.GetChannel]] expressions,
    * i.e.
    * {{{
    *   let pat1 = <- ch1;
    *   let pat2 = <- ch2;
    *   let pat3 = <- ch3;
    *   ...
    *   let patn = <- chn;
    *   exp
    * }}}
    */
  private def mkBoundParWaits(patSymExps: List[(MonoAst.Pattern, Symbol.VarSym, MonoAst.Expr, Type)], exp: MonoAst.Expr)(implicit ctx: Context): MonoAst.Expr =
    patSymExps.map {
      case (p, sym, e, rawTpe) =>
        val loc = e.loc.asSynthetic
        val chExp = mkChannelExp(sym, rawTpe, loc)
        (p, mkGetChannel(chExp, mkChannelTpe(rawTpe, loc), rawTpe, Type.IO, loc))
    }.foldRight(exp) {
      case ((pat, chan), e) => mkLetMatch(pat, chan, e)
    }

  /**
    * Returns a desugared let-match expression, i.e.
    * {{{
    *   let pattern = exp;
    *   body
    * }}}
    * is desugared to
    * {{{
    *   match exp {
    *     case pattern => body
    *   }
    * }}}
    */
  private def mkLetMatch(pat: MonoAst.Pattern, exp: MonoAst.Expr, body: MonoAst.Expr): MonoAst.Expr = {
    val loc = exp.loc.asSynthetic
    val rule = List(MonoAst.MatchRule(pat, None, body))
    val eff = Type.mkUnion(exp.eff, body.eff, loc)
    MonoAst.Expr.Match(exp, rule, body.tpe, eff, loc)
  }

  /**
    * An expression for a channel variable called `sym`.
    *
    * `tpe` is the RAW element type; the constructed channel type is rewritten here so this Var's
    * own type field matches how `mkNewChannel` actually specialized the channel `sym` is bound to
    * (which rewrites its own return type) — otherwise the let-bound value and every subsequent
    * reference to `sym` disagree on the channel's type (fresh sym vs. original).
    */
  private def mkChannelExp(sym: Symbol.VarSym, tpe: Type, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    MonoAst.Expr.Var(sym, SolutionSpecialization.rewriteEnumStructType(mkChannelTpe(tpe, loc)), loc)
  }

  /**
    * Returns a list expression constructed from the given `exps` with type list of `elmType`.
    *
    * @param elmType is assumed to be specialized and lowered.
    */
  private def mkList(exps: List[MonoAst.Expr], elmType: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val nil = mkNil(elmType, loc)
    exps.foldRight(nil) {
      case (e, acc) => mkCons(e, acc, elmType, loc)
    }
  }

  /**
    * Returns a `Nil` expression with type list of `elmType`.
    *
    * @param elmType is assumed to be specialized and lowered.
    */
  private def mkNil(elmType: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    mkTag(Enums.FList, "Nil", Nil, Types.mkList(elmType, loc), loc)
  }

  /**
    * Returns a `Cons(hd, tail)` expression with type list of `elmType`.
    *
    * `elmType` is threaded explicitly from `mkList` rather than read off `tail.tpe`: once `mkTag`
    * rewrites its own returned type (Step 2), `tail.tpe` for every cell but the innermost `Nil` is
    * already POST-rewrite (fresh sym, `Nil` args) — using it as the next `lookupCaseSym` key would
    * vacuously hit the "non-generic, keep original" branch and silently tag `Cons` with the wrong
    * (unspecialized) case sym while `Nil` got the fresh one.
    */
  private def mkCons(hd: MonoAst.Expr, tail: MonoAst.Expr, elmType: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    mkTag(Enums.FList, "Cons", List(hd, tail), Types.mkList(elmType, loc), loc)
  }

  /**
    * Returns a pure tag expression for the given `sym` and given `tag` with the given inner expression `exp`.
    *
    * @param tpe is assumed to be specialized and lowered, but NOT yet enum/struct-rewritten — this
    *            is the pre-rewrite ground type, used both as `lookupCaseSym`'s key and (rewritten)
    *            as the returned node's own type. `sym` is almost always non-generic (Datalog/PredSym/
    *            etc. runtime AST nodes), for which the tolerant lookup is a no-op fallback. The two
    *            exceptions that are actually generic are `Enums.FList` (`mkNil`/`mkCons`) and
    *            `Enums.Denotation` (`mkDenotation`'s `Relational` case): since `mkTag` synthesizes
    *            its own `AtomicOp.Tag` node directly rather than going through `visitExp`'s ordinary
    *            Tag case, it has to perform the case-sym lookup and the enum/struct-type rewrite
    *            itself.
    */
  private def mkTag(sym: Symbol.EnumSym, tag: String, exps: List[MonoAst.Expr], tpe: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val caseSym0 = findCaseSym(sym, tag)
    val caseSym = SolutionSpecialization.tolerant(SolutionSpecialization.lookupCaseSym(caseSym0, tpe), caseSym0)
    val t = SolutionSpecialization.rewriteEnumStructType(tpe)
    MonoAst.Expr.ApplyAtomic(AtomicOp.Tag(caseSym), exps, t, Type.Pure, loc)
  }

  /**
    * Returns the case symbol named `name` in the enum `sym`.
    */
  private def findCaseSym(sym: Symbol.EnumSym, name: String)(implicit root: TypedAst.Root): Symbol.CaseSym =
    root.enums(sym).cases.values.find(_.sym.name == name).get.sym

  /**
    * Returns `(t1, t2)` where `tpe = Concurrent.Channel.Mpmc[t1, t2]`.
    *
    * @param tpe is assumed to be specialized, but not lowered.
    */
  private def extractChannelTpe(tpe: Type): Type = tpe match {
    case Type.Apply(Type.Apply(Types.ChannelMpmc, elmType, _), _, _) => elmType
    case _ => throw InternalCompilerException(s"Cannot interpret '$tpe' as a channel type", tpe.loc)
  }

  /**
    * Returns a TypedAst.Pattern representing a tuple of patterns.
    *
    * @param patterns are assumed to contain specialized and lowered types.
    */
  private def mkTuplePattern(patterns: Nel[MonoAst.Pattern], loc: SourceLocation): MonoAst.Pattern = {
    MonoAst.Pattern.Tuple(patterns, Type.mkTuple(patterns.map(_.tpe), loc), loc)
  }

  /**
    * Returns a new `VarSym` for use in a let-binding.
    *
    * This function is called `mkLetSym` to avoid confusion with [[mkVarSym]].
    */
  private def mkLetSym(prefix: String, loc: SourceLocation)(implicit flix: Flix): Symbol.VarSym = {
    val name = prefix + Flix.Delimiter + flix.genSym.freshId()
    Symbol.freshVarSym(name, BoundBy.Let, loc)(RegionScope.Top, flix)
  }

  /**
    * The type of a channel which can transmit variables of type `tpe`.
    */
  private def mkChannelTpe(tpe: Type, loc: SourceLocation): Type = {
    Type.Apply(Type.Apply(Types.ChannelMpmc, tpe, loc), Type.IO, loc)
  }

  /*
    * Datalog lowering
    */

  /**
    * Constructs a `Fixpoint/Ast/Datalog.Datalog` value from the given list of Datalog constraints `cs`.
    */
  // ---- LOWERING: Datalog/fixpoint synthesis helpers ------------------------------------------
  private def lowerConstraintSet(cs: List[TypedAst.Constraint], loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val factExps = cs.filter(c => c.body.isEmpty).map(lowerConstraint(_, env0, subst))
    val ruleExps = cs.filter(c => c.body.nonEmpty).map(lowerConstraint(_, env0, subst))

    val factListExp = mkVector(factExps, Types.Constraint, loc)
    val ruleListExp = mkVector(ruleExps, Types.Constraint, loc)

    val innerExp = List(factListExp, ruleListExp)
    mkTag(Enums.Datalog, "Datalog", innerExp, Types.Datalog, loc)
  }

  /**
    *
    * Create appropriate call to Fixpoint.Solver.provenanceOf. This requires creating a mapping, mkExtVar, from
    * PredSym and terms to an extensible variant.
    */
  // NB (fused walk): `tpe0`/`eff` must arrive already substituted from the caller; `env0`/`subst`
  // are only for the TypedAst sub-expressions visited here.
  private def lowerQueryWithProvenance(exps: List[TypedAst.Expr], select: Predicate.Head, withh: List[Name.Pred], tpe0: Type, eff: Type, loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val tpe = lowerType(tpe0)
    val mergedExp = mergeExps(exps.map(visitExp(_, env0, subst)), loc)
    val (goalPredSym, goalTerms) = select match {
      case TypedAst.Predicate.Head.Atom(pred, _, terms, _, loc1) =>
        val boxedTerms = terms.map(t => box(visitExp(t, env0, subst), subst(t.tpe)))
        (mkPredSym(pred), mkVector(boxedTerms, Types.Boxed, loc1))
    }
    val withPredSyms = mkVector(withh.map(mkPredSym), Types.PredSym, loc)
    val extVarType = unwrapVectorType(tpe, loc)
    val preds = predicatesOfExtVar(extVarType, loc)
    val lambdaExp = mkExtVarLambda(preds, extVarType, loc)
    val argExps = goalPredSym :: goalTerms :: withPredSyms :: lambdaExp :: mergedExp :: Nil
    val itpe = Types.mkProvenanceOf(extVarType, loc)
    val defn = lookup(Defs.ProvenanceOf, itpe)
    MonoAst.Expr.ApplyDef(defn, argExps, SolutionSpecialization.rewriteEnumStructType(itpe), SolutionSpecialization.rewriteEnumStructType(tpe), eff, loc)
  }

  // NB (fused walk): `tpe`/`eff` must arrive already substituted from the caller.
  private def lowerQueryWithSelect(exps: List[TypedAst.Expr], queryExp: TypedAst.Expr, selects: List[TypedAst.Expr], pred: Name.Pred, tpe: Type, eff: Type, loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val loweredExps = exps.map(visitExp(_, env0, subst))
    val loweredQueryExp = visitExp(queryExp, env0, subst)

    val predArity = selects.length

    // Define the name and type of the appropriate factsX function in Solver.flix
    val defTpe = Type.mkPureUncurriedArrow(List(Types.PredSym, Types.Datalog), tpe, loc)
    val sym = lookup(Defs.Facts(predArity), defTpe)

    // Merge and solve exps
    val mergedExp = mergeExps(loweredQueryExp :: loweredExps, loc)
    val solveDefn = lookup(Defs.Solve, Types.SolveType)
    val solvedExp = MonoAst.Expr.ApplyDef(solveDefn, mergedExp :: Nil, Types.SolveType, Types.Datalog, eff, loc)

    // Put everything together
    val argExps = mkPredSym(pred) :: solvedExp :: Nil
    MonoAst.Expr.ApplyDef(sym, argExps, SolutionSpecialization.rewriteEnumStructType(defTpe), SolutionSpecialization.rewriteEnumStructType(tpe), eff, loc)

  }

  /**
    * Rewrites
    * {{{
    *     solve e₁, e₂, e₃ project P₁, P₂, P₃
    * }}}
    * to
    * {{{
    *     let tmp% = solve e₁ <+> e₂ <+> e₃;
    *     merge (project P₁ tmp%, project P₂ tmp%, project P₃ tmp%)
    * }}}
    */
  // NB (fused walk): `eff` must arrive already substituted from the caller.
  private def lowerSolveWithProject(exps0: List[TypedAst.Expr], optPreds: Option[List[Name.Pred]], mode: SolveMode, eff: Type, loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val defn = mode match {
      case SolveMode.Default => lookup(Defs.Solve, Types.Datalog)
      case SolveMode.WithProvenance => lookup(Defs.SolveWithProvenance, Types.Datalog)
    }
    val exps = exps0.map(visitExp(_, env0, subst))
    val mergedExp = mergeExps(exps, loc)
    val argExps = mergedExp :: Nil
    val solvedExp = MonoAst.Expr.ApplyDef(defn, argExps, Types.SolveType, Types.Datalog, eff, loc)
    val tmpVarSym = Symbol.freshVarSym("tmp%", BoundBy.Let, loc)(RegionScope.Top, flix)
    val letBodyExp = optPreds match {
      case Some(preds) =>
        mergeExps(preds.map(pred => {
          val varExp = MonoAst.Expr.Var(tmpVarSym, Types.Datalog, loc)
          projectSym(mkPredSym(pred), varExp, loc)
        }), loc)
      case None => MonoAst.Expr.Var(tmpVarSym, Types.Datalog, loc)
    }
    MonoAst.Expr.Let(tmpVarSym, solvedExp, letBodyExp, Types.Datalog, eff, Occur.Unknown, loc)

  }

  private def lowerInjectInto(exps: List[TypedAst.Expr], predsAndArities: List[PredicateAndArity], loc: SourceLocation, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val loweredExps = exps.zip(predsAndArities).map {
      case (exp, PredicateAndArity(pred, _)) =>
        // The exp's own type/eff are TypedAst-level reads: substitute before use (fused walk).
        val expTpe = subst(exp.tpe)
        // Compute the types arguments of the functor F[(a, b, c)] or F[a].
        val (_, targsLength) = expTpe match {
          case Type.Apply(tycon, innerType, _) => innerType.typeConstructor match {
            case Some(TypeConstructor.Tuple(_)) => (tycon, innerType.typeArguments.length)
            case Some(TypeConstructor.Unit) => (tycon, 0)
            case _ => (tycon, 1)
          }
          case _ => throw InternalCompilerException(s"Unexpected non-foldable type: '$expTpe'.", loc)
        }

        // The type of the function.
        val defTpe = Type.mkPureUncurriedArrow(List(Types.PredSym, lowerType(expTpe)), Types.Datalog, loc)

        // Compute the symbol of the function.
        val sym = lookup(Defs.ProjectInto(targsLength), defTpe)

        // Put everything together.
        val argExps = mkPredSym(pred) :: visitExp(exp, env0, subst) :: Nil
        MonoAst.Expr.ApplyDef(sym, argExps, SolutionSpecialization.rewriteEnumStructType(defTpe), Types.Datalog, subst(exp.eff), loc)
    }
    mergeExps(loweredExps, loc)

  }

  /**
    * Specializes and lowers the given constraint `c0`.
    */
  private def lowerConstraint(c0: TypedAst.Constraint, env0: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = c0 match {
    case TypedAst.Constraint(cparams, head, body, loc) =>
      // Freshen the constraint params (the quantified vars) up front — head and body must share
      // this env.
      val env = cparams.foldLeft(env0) {
        case (env1, TypedAst.ConstraintParam(bnd, _, _)) =>
          if (env1.contains(bnd.sym)) env1
          else { val freshSym = Symbol.freshVarSym(bnd.sym); env1 + (bnd.sym -> freshSym) }
      }
      val headExp = lowerHeadPred(cparams, head, env, subst)
      val bodyExp = mkVector(body.map(lowerBodyPred(cparams, _, env, subst)), Types.BodyPredicate, loc)
      val innerExp = List(headExp, bodyExp)
      mkTag(Enums.Constraint, "Constraint", innerExp, Types.Constraint, loc)
  }

  /**
    * Lowers the given head predicate `p0`.
    */
  private def lowerHeadPred(cparams0: List[TypedAst.ConstraintParam], p0: TypedAst.Predicate.Head, env: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = p0 match {
    case TypedAst.Predicate.Head.Atom(pred, den, terms, _, loc) =>
      val predSymExp = mkPredSym(pred)
      val denotationExp = mkDenotation(den, terms.lastOption.map(t => subst(t.tpe)), loc)
      val termsExp = mkVector(terms.map(lowerHeadTerm(cparams0, _, env, subst)), Types.HeadTerm, loc)
      val innerExp = List(predSymExp, denotationExp, termsExp)
      mkTag(Enums.HeadPredicate, "HeadAtom", innerExp, Types.HeadPredicate, loc)
  }

  /**
    * Lowers the given body predicate `p0`.
    */
  private def lowerBodyPred(cparams0: List[TypedAst.ConstraintParam], p0: TypedAst.Predicate.Body, env: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = p0 match {
    case TypedAst.Predicate.Body.Atom(pred, den, polarity, fixity, terms, _, loc) =>
      val predSymExp = mkPredSym(pred)
      val denotationExp = mkDenotation(den, terms.lastOption.map(t => subst(t.tpe)), loc)
      val polarityExp = mkPolarity(polarity, loc)
      val fixityExp = mkFixity(fixity, loc)
      val termsExp = mkVector(terms.map(lowerBodyTerm(cparams0, _, env, subst)), Types.BodyTerm, loc)
      val innerExp = List(predSymExp, denotationExp, polarityExp, fixityExp, termsExp)
      mkTag(Enums.BodyPredicate, "BodyAtom", innerExp, Types.BodyPredicate, loc)

    case TypedAst.Predicate.Body.Functional(outVars0, exp0, loc) =>
      // Compute the universally quantified variables (i.e. the variables not bound by the local scope).
      // NB: quantified on RAW syms (cparams vs. exp0), then mapped through env/subst — the syms
      // must match the visited exp's renamed vars inside mkFunctional's substExp.
      val inVars = quantifiedVars(cparams0, exp0).map { case (sym, tpe) => (env(sym), subst(tpe)) }
      val exp = visitExp(exp0, env, subst)
      val outVars = outVars0.map(b => env(b.sym))
      mkFunctional(outVars, inVars, exp, subst(exp0.tpe), loc)

    case TypedAst.Predicate.Body.Guard(exp0, loc) =>
      // Compute the universally quantified variables (i.e. the variables not bound by the local scope).
      // NB: same env/subst mapping as Functional above, for the same reason (mkGuard's substExp).
      val quantifiedFreeVars = quantifiedVars(cparams0, exp0).map { case (sym, tpe) => (env(sym), subst(tpe)) }
      val exp = visitExp(exp0, env, subst)
      mkGuard(quantifiedFreeVars, exp, loc)

  }

  /**
    * Lowers the given head term `exp0`.
    */
  private def lowerHeadTerm(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr, env: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, lctx: LocalContext, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    //
    // We need to consider four cases:
    //
    // Case 1.1: The expression is quantified variable. We translate it to a Var.
    // Case 1.2: The expression is a lexically bound variable. We translate it to a Lit that captures its value.
    // Case 2: The expression does not contain a quantified variable. We evaluate it to a (boxed) value.
    // Case 3: The expression contains quantified variables. We translate it to an application term.
    //
    exp0 match {
      case TypedAst.Expr.Var(sym, _, _) =>
        // Case 1: Variable term.
        if (isQuantifiedVar(sym, cparams0)) {
          // Case 1.1: Quantified variable.
          mkHeadTermVar(env(sym))
        } else {
          // Case 1.2: Lexically bound variable.
          mkHeadTermLit(box(visitExp(exp0, env, subst), subst(exp0.tpe)))
        }

      case _ =>
        // Compute the universally quantified variables (i.e. the variables not bound by the local scope).
        val quantifiedFreeVars = quantifiedVars(cparams0, exp0)

        if (quantifiedFreeVars.isEmpty) {
          // Case 2: No quantified variables. The expression can be reduced to a value.
          mkHeadTermLit(box(visitExp(exp0, env, subst), subst(exp0.tpe)))
        } else {
          // Case 3: Quantified variables. The expression is translated to an application term.
          // NB: env/subst-mapped so the syms match the visited exp inside mkAppTerm's substExp.
          val fvs = quantifiedFreeVars.map { case (sym, tpe) => (env(sym), subst(tpe)) }
          mkAppTerm(fvs, visitExp(exp0, env, subst), subst(exp0.tpe), exp0.loc)
        }
    }
  }

  /**
    * Lowers the given body term `pat0`.
    */
  private def lowerBodyTerm(cparams0: List[TypedAst.ConstraintParam], pat0: TypedAst.Pattern, env: Map[Symbol.VarSym, Symbol.VarSym], subst: StrictSubstitution)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = pat0 match {
    case TypedAst.Pattern.Wild(_, loc) =>
      mkBodyTermWild(loc)

    case TypedAst.Pattern.Var(bnd, tpe, loc) =>
      if (isQuantifiedVar(bnd.sym, cparams0)) {
        // Case 1: Quantified variable.
        mkBodyTermVar(env(bnd.sym))
      } else {
        // Case 2: Lexically bound variable *expression* — references an enclosing binder, so it
        // must be renamed; the type is a TypedAst read, so it must be substituted but not lowered.
        val rawTpe = subst(tpe)
        mkBodyTermLit(box(MonoAst.Expr.Var(env(bnd.sym), visitTypeSubstituted(rawTpe), loc), rawTpe))
      }

    case TypedAst.Pattern.Cst(cst, tpe, loc) =>
      val rawTpe = subst(tpe)
      mkBodyTermLit(box(MonoAst.Expr.Cst(cst, visitTypeSubstituted(rawTpe), loc), rawTpe))

    case TypedAst.Pattern.Tag(_, _, _, loc) => throw InternalCompilerException(s"Unexpected pattern: '$pat0'.", loc)

    case TypedAst.Pattern.Tuple(_, _, loc) => throw InternalCompilerException(s"Unexpected pattern: '$pat0'.", loc)

    case TypedAst.Pattern.Record(_, _, _, loc) => throw InternalCompilerException(s"Unexpected pattern: '$pat0'.", loc)

    case TypedAst.Pattern.Error(_, loc) =>
      throw InternalCompilerException(s"Unexpected pattern: '$pat0'.", loc)

  }

  /**
    * Returns an expression merging `exps` using `Defs.Merge`.
    */
  private def mergeExps(exps: List[MonoAst.Expr], loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr =
    exps.reduceRight {
      (exp, acc) =>
        val resultType = Types.Datalog
        val defn = lookup(Defs.Merge, resultType)
        val argExps = exp :: acc :: Nil
        val itpe = Types.MergeType
        MonoAst.Expr.ApplyDef(defn, argExps, itpe, resultType, exp.eff, loc)
    }

  /**
    * Returns a new `Datalog` from `datalogExp` containing only facts from the predicate given by the `PredSym` `predSymExp`
    * using `Defs.Filter`.
    */
  private def projectSym(predSymExp: MonoAst.Expr, datalogExp: MonoAst.Expr, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    val resultType = Types.Datalog
    val defn = lookup(Defs.Filter, resultType)
    val argExps = predSymExp :: datalogExp :: Nil
    val itpe = Types.FilterType
    MonoAst.Expr.ApplyDef(defn, argExps, itpe, resultType, datalogExp.eff, loc)
  }

  /**
    * Lifts the given lambda expression `exp0` with the given argument types `argTypes`.
    *
    * Note: liftX and liftXb are similar and should probably be maintained together.
    */
  private def liftX(exp0: MonoAst.Expr, argTypes: List[Type], resultType: Type)(implicit ctx: Context): MonoAst.Expr = {
    //
    // The liftX family of functions are of the form: a -> b -> c -> `resultType` and
    // returns a function of the form Boxed -> Boxed -> Boxed -> Boxed -> Boxed`.
    // That is, the function accepts a *curried* function and returns a *curried* function.
    //

    // The type of the function argument, i.e. a -> b -> c -> `resultType`.
    val argType = Type.mkPureCurriedArrow(argTypes, resultType, exp0.loc)

    // The type of the returned function, i.e. Boxed -> Boxed -> Boxed -> Boxed.
    val returnType = Type.mkPureCurriedArrow(argTypes.map(_ => Types.Boxed), Types.Boxed, exp0.loc)

    // The type of the overall liftX function, i.e. (a -> b -> c -> `resultType`) -> (Boxed -> Boxed -> Boxed -> Boxed).
    val liftType = Type.mkPureArrow(argType, returnType, exp0.loc)

    // Compute the liftXb symbol.
    val sym = lookup(Symbol.mkDefnSym(s"Fixpoint${Defs.version}.Boxable.lift${argTypes.length}"), liftType)

    // Construct a call to the liftX function.
    MonoAst.Expr.ApplyDef(sym, List(exp0), SolutionSpecialization.rewriteEnumStructType(liftType), returnType, Type.Pure, exp0.loc)
  }

  /**
    * Lifts the given Boolean-valued lambda expression `exp0` with the given argument types `argTypes`.
    */
  private def liftXb(exp0: MonoAst.Expr, argTypes: List[Type])(implicit ctx: Context): MonoAst.Expr = {
    //
    // The liftX family of functions are of the form: a -> b -> c -> Bool and
    // returns a function of the form Boxed -> Boxed -> Boxed -> Boxed -> Bool.
    // That is, the function accepts a *curried* function and returns a *curried* function.
    //

    // The type of the function argument, i.e. a -> b -> c -> Bool.
    val argType = Type.mkPureCurriedArrow(argTypes, Type.Bool, exp0.loc)

    // The type of the returned function, i.e. Boxed -> Boxed -> Boxed -> Bool.
    val returnType = Type.mkPureCurriedArrow(argTypes.map(_ => Types.Boxed), Type.Bool, exp0.loc)

    // The type of the overall liftXb function, i.e. (a -> b -> c -> Bool) -> (Boxed -> Boxed -> Boxed -> Bool).
    val liftType = Type.mkPureArrow(argType, returnType, exp0.loc)

    // Compute the liftXb symbol.
    val sym = lookup(Symbol.mkDefnSym(s"Fixpoint${Defs.version}.Boxable.lift${argTypes.length}b"), liftType)

    // Construct a call to the liftXb function.
    MonoAst.Expr.ApplyDef(sym, List(exp0), SolutionSpecialization.rewriteEnumStructType(liftType), returnType, Type.Pure, exp0.loc)
  }

  /**
    * Lifts the given lambda expression `exp0` with the given argument types `argTypes` and `resultType`.
    */
  private def liftXY(outVars: List[Symbol.VarSym], exp0: MonoAst.Expr, argTypes: List[Type], resultType: Type, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    //
    // The liftXY family of functions are of the form: i1 -> i2 -> i3 -> Vector[(o1, o2, o3, ...)] and
    // returns a function of the form Vector[Boxed] -> Vector[Vector[Boxed]].
    // That is, the function accepts a *curried* function and an uncurried function that takes
    // its input as a boxed Vector and return its output as a vector of vectors.
    //

    // The type of the function argument, i.e. i1 -> i2 -> i3 -> Vector[(o1, o2, o3, ...)].
    val argType = Type.mkPureCurriedArrow(argTypes, resultType, loc)

    // The type of the returned function, i.e. Vector[Boxed] -> Vector[Vector[Boxed]].
    val returnType = Type.mkPureArrow(Type.mkVector(Types.Boxed, loc), Type.mkVector(Type.mkVector(Types.Boxed, loc), loc), loc)

    // The type of the overall liftXY function, i.e. (i1 -> i2 -> i3 -> Vector[(o1, o2, o3, ...)]) -> (Vector[Boxed] -> Vector[Vector[Boxed]]).
    val liftType = Type.mkPureArrow(argType, returnType, loc)

    // Compute the number of bound ("output") and free ("input") variables.
    val numberOfInVars = argTypes.length
    val numberOfOutVars = outVars.length

    // Compute the liftXY symbol.
    // For example, lift3X2 is a function from three arguments to a Vector of pairs.
    val sym = lookup(Symbol.mkDefnSym(s"Fixpoint${Defs.version}.Boxable.lift${numberOfInVars}X$numberOfOutVars"), liftType)

    // Construct a call to the liftXY function.
    MonoAst.Expr.ApplyDef(sym, List(exp0), SolutionSpecialization.rewriteEnumStructType(liftType), returnType, Type.Pure, loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.HeadTerm.Var` from the given variable symbol `sym`.
    */
  private def mkHeadTermVar(sym: Symbol.VarSym)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val innerExp = List(mkVarSym(sym))
    mkTag(Enums.HeadTerm, "Var", innerExp, Types.HeadTerm, sym.loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.HeadTerm.Lit` value which wraps the given expression `exp`.
    */
  private def mkHeadTermLit(exp: MonoAst.Expr)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    mkTag(Enums.HeadTerm, "Lit", List(exp), Types.HeadTerm, exp.loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.BodyTerm.Wild` from the given source location `loc`.
    */
  private def mkBodyTermWild(loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    mkTag(Enums.BodyTerm, "Wild", Nil, Types.BodyTerm, loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.BodyTerm.Var` from the given variable symbol `sym`.
    */
  private def mkBodyTermVar(sym: Symbol.VarSym)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val innerExp = List(mkVarSym(sym))
    mkTag(Enums.BodyTerm, "Var", innerExp, Types.BodyTerm, sym.loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.BodyTerm.Lit` from the given expression `exp0`.
    */
  private def mkBodyTermLit(exp: MonoAst.Expr)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    mkTag(Enums.BodyTerm, "Lit", List(exp), Types.BodyTerm, exp.loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.VarSym` from the given variable symbol `sym`.
    */
  private def mkVarSym(sym: Symbol.VarSym)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = {
    val nameExp = MonoAst.Expr.Cst(Constant.Str(sym.text), Type.Str, sym.loc)
    mkTag(Enums.VarSym, "VarSym", List(nameExp), Types.VarSym, sym.loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Shared.Denotation` from the given denotation `d` and type `tpeOpt`
    * (which must be the optional type of the last term).
    */
  private def mkDenotation(d: Denotation, tpeOpt: Option[Type], loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = d match {
    case Denotation.Relational =>
      mkTag(Enums.Denotation, "Relational", Nil, Types.Denotation, loc)

    case Denotation.Latticenal =>
      tpeOpt match {
        case None => throw InternalCompilerException("Unexpected nullary lattice predicate.", loc)
        case Some(tpe) =>
          val innerType = lowerType(tpe)
          // The type `Denotation[tpe]`.
          val unboxedDenotationType = Type.mkEnum(Enums.Denotation, innerType :: Nil, loc)

          // The type `Denotation[Boxed]`.
          val boxedDenotationType = Types.Denotation

          val latticeType: Type = Type.mkPureArrow(Type.Unit, unboxedDenotationType, loc)
          val latticeSym: Symbol.DefnSym = lookup(Symbol.mkDefnSym(s"Fixpoint${Defs.version}.Ast.Shared.lattice"), latticeType)

          val boxType: Type = Type.mkPureArrow(unboxedDenotationType, boxedDenotationType, loc)
          val boxSym: Symbol.DefnSym = lookup(Symbol.mkDefnSym(s"Fixpoint${Defs.version}.Ast.Shared.box"), boxType)

          val innerApply = MonoAst.Expr.ApplyDef(latticeSym, List(MonoAst.Expr.Cst(Constant.Unit, Type.Unit, loc)), SolutionSpecialization.rewriteEnumStructType(latticeType), SolutionSpecialization.rewriteEnumStructType(unboxedDenotationType), Type.Pure, loc)
          MonoAst.Expr.ApplyDef(boxSym, List(innerApply), SolutionSpecialization.rewriteEnumStructType(boxType), SolutionSpecialization.rewriteEnumStructType(boxedDenotationType), Type.Pure, loc)
      }
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.Polarity` from the given polarity `p`.
    */
  private def mkPolarity(p: Polarity, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = p match {
    case Polarity.Positive =>
      mkTag(Enums.Polarity, "Positive", Nil, Types.Polarity, loc)

    case Polarity.Negative =>
      mkTag(Enums.Polarity, "Negative", Nil, Types.Polarity, loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Datalog.Fixity` from the given fixity `f`.
    */
  private def mkFixity(f: Fixity, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = f match {
    case Fixity.Loose =>
      mkTag(Enums.Fixity, "Loose", Nil, Types.Fixity, loc)

    case Fixity.Fixed =>
      mkTag(Enums.Fixity, "Fixed", Nil, Types.Fixity, loc)
  }

  /**
    * Returns a `Fixpoint/Ast/Datalog.BodyPredicate.GuardX`.
    */
  private def mkGuard(fvs: List[(Symbol.VarSym, Type)], exp: MonoAst.Expr, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    // Compute the number of free variables.
    val arity = fvs.length

    // Check that we have <= 5 free variables.
    if (arity > 5) {
      throw InternalCompilerException("Cannot lift functions with more than 5 free variables.", loc)
    }

    // Special case: No free variables.
    if (fvs.isEmpty) {
      val sym = Symbol.freshVarSym("_unit", BoundBy.FormalParam, loc)(RegionScope.Top, flix)
      // Construct a lambda that takes the unit argument.
      val fparam = MonoAst.FormalParam(sym, Type.Unit, Occur.Unknown, loc)
      val tpe = Type.mkPureArrow(Type.Unit, exp.tpe, loc)
      val lambdaExp = MonoAst.Expr.Lambda(fparam, exp, tpe, loc)
      return mkTag(Enums.BodyPredicate, s"Guard0", List(lambdaExp), Types.BodyPredicate, loc)
    }

    // Introduce a fresh variable for each free variable.
    val freshVars = fvs.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (acc, (oldSym, _)) => acc + (oldSym -> Symbol.freshVarSym(oldSym))
    }

    // Substitute every symbol in `exp` for its fresh equivalent.
    val freshExp = substExp(exp, freshVars)

    // Curry `freshExp` in a lambda expression for each free variable.
    val lambdaExp = fvs.foldRight(freshExp) {
      case ((oldSym, tpe), acc) =>
        val freshSym = freshVars(oldSym)
        // tpe is RAW (correct as the liftX/liftXY lookup-key component below) but this
        // FormalParam/Lambda's own type fields need the enum/struct rewrite for consistency.
        val rewrittenTpe = SolutionSpecialization.rewriteEnumStructType(tpe)
        val fparam = MonoAst.FormalParam(freshSym, rewrittenTpe, Occur.Unknown, loc)
        val lambdaType = Type.mkPureArrow(rewrittenTpe, acc.tpe, loc)
        MonoAst.Expr.Lambda(fparam, acc, lambdaType, loc)
    }

    // Lift the lambda expression to operate on boxed values.
    val liftedExp = liftXb(lambdaExp, fvs.map(_._2))

    // Construct the `Fixpoint/Ast/Datalog.BodyPredicate` value.
    val varExps = fvs.map(kv => mkVarSym(kv._1))
    val innerExp = liftedExp :: varExps
    mkTag(Enums.BodyPredicate, s"Guard$arity", innerExp, Types.BodyPredicate, loc)
  }

  /**
    * Returns a `Fixpoint/Ast/Datalog.BodyPredicate.Functional`.
    */
  private def mkFunctional(outVars: List[Symbol.VarSym], inVars: List[(Symbol.VarSym, Type)], exp: MonoAst.Expr, rawResultTpe: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    // Compute the number of in and out variables.
    val numberOfInVars = inVars.length
    val numberOfOutVars = outVars.length

    if (numberOfInVars > 5) {
      throw InternalCompilerException("Does not support more than 5 in variables.", loc)
    }
    if (numberOfOutVars == 0) {
      throw InternalCompilerException("Requires at least one out variable.", loc)
    }
    if (numberOfOutVars > 5) {
      throw InternalCompilerException("Does not support more than 5 out variables.", loc)
    }

    // Introduce a fresh variable for each in variable.
    val freshVars = inVars.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (acc, (oldSym, _)) => acc + (oldSym -> Symbol.freshVarSym(oldSym))
    }

    // Substitute every symbol in `exp` for its fresh equivalent.
    val freshExp = substExp(exp, freshVars)

    // Curry `freshExp` in a lambda expression for each free variable.
    val lambdaExp = inVars.foldRight(freshExp) {
      case ((oldSym, tpe), acc) =>
        val freshSym = freshVars(oldSym)
        // tpe is RAW (correct as the liftX/liftXY lookup-key component below) but this
        // FormalParam/Lambda's own type fields need the enum/struct rewrite for consistency.
        val rewrittenTpe = SolutionSpecialization.rewriteEnumStructType(tpe)
        val fparam = MonoAst.FormalParam(freshSym, rewrittenTpe, Occur.Unknown, loc)
        val lambdaType = Type.mkPureArrow(rewrittenTpe, acc.tpe, loc)
        MonoAst.Expr.Lambda(fparam, acc, lambdaType, loc)
    }

    // Lift the lambda expression to operate on boxed values.
    // NB: rawResultTpe (not exp.tpe, already enum/struct-rewritten) — see box's doc comment.
    val liftedExp = liftXY(outVars, lambdaExp, inVars.map(_._2), rawResultTpe, exp.loc)

    // Construct the `Fixpoint/Ast/Datalog.BodyPredicate` value.
    val boundVarVector = mkVector(outVars.map(mkVarSym), Types.VarSym, loc)
    val freeVarVector = mkVector(inVars.map(kv => mkVarSym(kv._1)), Types.VarSym, loc)
    val innerExp = List(boundVarVector, liftedExp, freeVarVector)
    mkTag(Enums.BodyPredicate, s"Functional", innerExp, Types.BodyPredicate, loc)
  }

  /**
    * Returns a `Fixpoint/Ast/Datalog.HeadTerm.AppX`.
    */
  private def mkAppTerm(fvs: List[(Symbol.VarSym, Type)], exp: MonoAst.Expr, rawResultTpe: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    // Compute the number of free variables.
    val arity = fvs.length

    // Check that we have <= 5 free variables.
    if (arity > 5) {
      throw InternalCompilerException("Cannot lift functions with more than 5 free variables.", loc)
    }

    // Introduce a fresh variable for each free variable.
    val freshVars = fvs.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (acc, (oldSym, _)) => acc + (oldSym -> Symbol.freshVarSym(oldSym))
    }

    // Substitute every symbol in `exp` for its fresh equivalent.
    val freshExp = substExp(exp, freshVars)

    // Curry `freshExp` in a lambda expression for each free variable.
    val lambdaExp = fvs.foldRight(freshExp) {
      case ((oldSym, tpe), acc) =>
        val freshSym = freshVars(oldSym)
        // tpe is RAW (correct as the liftX/liftXY lookup-key component below) but this
        // FormalParam/Lambda's own type fields need the enum/struct rewrite for consistency.
        val rewrittenTpe = SolutionSpecialization.rewriteEnumStructType(tpe)
        val fparam = MonoAst.FormalParam(freshSym, rewrittenTpe, Occur.Unknown, loc)
        val lambdaType = Type.mkPureArrow(rewrittenTpe, acc.tpe, loc)
        MonoAst.Expr.Lambda(fparam, acc, lambdaType, loc)
    }

    // Lift the lambda expression to operate on boxed values.
    // NB: rawResultTpe (not exp.tpe, already enum/struct-rewritten) — see box's doc comment.
    val liftedExp = liftX(lambdaExp, fvs.map(_._2), rawResultTpe)

    // Construct the `Fixpoint/Ast/Datalog.BodyPredicate` value.
    val varExps = fvs.map(kv => mkVarSym(kv._1))
    val innerExp = liftedExp :: varExps
    mkTag(Enums.HeadTerm, s"App$arity", innerExp, Types.HeadTerm, loc)
  }

  /**
    * Constructs a `Fixpoint/Ast/Shared.PredSym` from the given predicate `pred`.
    */
  private def mkPredSym(pred: Name.Pred)(implicit ctx: Context, root: TypedAst.Root): MonoAst.Expr = pred match {
    case Name.Pred(sym, loc) =>
      val nameExp = MonoAst.Expr.Cst(Constant.Str(sym), Type.Str, loc)
      val idExp = MonoAst.Expr.Cst(Constant.Int64(0), Type.Int64, loc)
      val inner = List(nameExp, idExp)
      mkTag(Enums.PredSym, "PredSym", inner, Types.PredSym, loc)
  }

  /**
    * Returns the given expression `exp` in a box.
    *
    * @param rawTpe `exp`'s RAW substituted (pre-visit) type — NOT `exp.tpe`, which is already
    *               enum/struct-rewritten by the time an already-visited `exp` reaches here. Used
    *               as `Boxable.box`'s def-lookup key; see mkGetChannel's doc comment for why the
    *               already-rewritten `.tpe` can't be reused for this.
    */
  private def box(exp: MonoAst.Expr, rawTpe: Type)(implicit ctx: Context): MonoAst.Expr = {
    val loc = exp.loc
    val tpe = Type.mkPureArrow(rawTpe, Types.Boxed, loc)
    MonoAst.Expr.ApplyDef(lookup(Defs.Box, tpe), List(exp), SolutionSpecialization.rewriteEnumStructType(tpe), Types.Boxed, Type.Pure, loc)
  }

  /**
    * Returns a vector expression constructed from the given `exps` with type list of `elmType`.
    */
  private def mkVector(exps: List[MonoAst.Expr], elmType: Type, loc: SourceLocation): MonoAst.Expr = {
    MonoAst.Expr.ApplyAtomic(AtomicOp.VectorLit, exps, Type.mkVector(elmType, loc), Type.Pure, loc)
  }

  /**
    * Return a list of quantified variables in the given expression `exp0`.
    *
    * A variable is quantified (i.e. *NOT* lexically bound) if it occurs in the expression `exp0`
    * but not in the constraint params `cparams0` of the constraint.
    */
  private def quantifiedVars(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr): List[(Symbol.VarSym, Type)] = {
    TypedAstOps.freeVars(exp0).toList.filter {
      case (sym, _) => isQuantifiedVar(sym, cparams0)
    }
  }

  /**
    * Returns `true` if the given variable symbol `sym` is a quantified variable according to the given constraint params `cparams0`.
    *
    * That is, the variable symbol is *NOT* lexically bound.
    */
  private def isQuantifiedVar(sym: Symbol.VarSym, cparams0: List[TypedAst.ConstraintParam]): Boolean =
    cparams0.exists(p => p.bnd.sym == sym)

  /*
   * Methods for substitution
   */

  /**
    * Applies the given substitution `subst` to the given expression `exp0`.
    */
  private def substExp(exp0: MonoAst.Expr, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.Expr = exp0 match {
    case MonoAst.Expr.Cst(_, _, _) => exp0

    case MonoAst.Expr.Var(sym, tpe, loc) =>
      val s = subst.getOrElse(sym, sym)
      MonoAst.Expr.Var(s, tpe, loc)

    case MonoAst.Expr.Lambda(fparam, exp, tpe, loc) =>
      val p = substFormalParam(fparam, subst)
      val e = substExp(exp, subst)
      MonoAst.Expr.Lambda(p, e, tpe, loc)

    case MonoAst.Expr.ApplyClo(exp1, exp2, tpe, eff, loc) =>
      val e1 = substExp(exp1, subst)
      val e2 = substExp(exp2, subst)
      MonoAst.Expr.ApplyClo(e1, e2, tpe, eff, loc)

    case MonoAst.Expr.ApplyDef(sym, exps, itpe, tpe, eff, loc) =>
      val es = exps.map(substExp(_, subst))
      MonoAst.Expr.ApplyDef(sym, es, itpe, tpe, eff, loc)

    case MonoAst.Expr.ApplyLocalDef(sym, exps, tpe, eff, loc) =>
      val es = exps.map(substExp(_, subst))
      MonoAst.Expr.ApplyLocalDef(sym, es, tpe, eff, loc)

    case MonoAst.Expr.ApplyOp(sym, exps, tpe, eff, loc) =>
      val es = exps.map(substExp(_, subst))
      MonoAst.Expr.ApplyOp(sym, es, tpe, eff, loc)

    case MonoAst.Expr.ApplyAtomic(op, exps, tpe, eff, loc) =>
      val es = exps.map(substExp(_, subst))
      MonoAst.Expr.ApplyAtomic(op, es, tpe, eff, loc)

    case MonoAst.Expr.Let(sym, exp1, exp2, tpe, eff, occur, loc) =>
      val s = subst.getOrElse(sym, sym)
      val e1 = substExp(exp1, subst)
      val e2 = substExp(exp2, subst)
      MonoAst.Expr.Let(s, e1, e2, tpe, eff, occur, loc)

    case MonoAst.Expr.LocalDef(sym, fparams, exp1, exp2, tpe, eff, occur, loc) =>
      val s = subst.getOrElse(sym, sym)
      val fps = fparams.map(substFormalParam(_, subst))
      val e1 = substExp(exp1, subst)
      val e2 = substExp(exp2, subst)
      MonoAst.Expr.LocalDef(s, fps, e1, e2, tpe, eff, occur, loc)

    case MonoAst.Expr.Region(sym, regionVar, exp, tpe, eff, loc) =>
      val s = subst.getOrElse(sym, sym)
      val e = substExp(exp, subst)
      MonoAst.Expr.Region(s, regionVar, e, tpe, eff, loc)

    case MonoAst.Expr.IfThenElse(exp1, exp2, exp3, tpe, eff, loc) =>
      val e1 = substExp(exp1, subst)
      val e2 = substExp(exp2, subst)
      val e3 = substExp(exp3, subst)
      MonoAst.Expr.IfThenElse(e1, e2, e3, tpe, eff, loc)

    case MonoAst.Expr.Stm(exps, exp, tpe, eff, loc) =>
      val es = exps.map(substExp(_, subst))
      val e = substExp(exp, subst)
      MonoAst.Expr.Stm(es, e, tpe, eff, loc)

    case MonoAst.Expr.Discard(exp, eff, loc) =>
      val e = substExp(exp, subst)
      MonoAst.Expr.Discard(e, eff, loc)

    case MonoAst.Expr.Match(exp, rules, tpe, eff, loc) =>
      val e = substExp(exp, subst)
      val rs = rules.map {
        case MonoAst.MatchRule(pat, guard, exp1) =>
          val p = substPattern(pat, subst)
          val g = guard.map(substExp(_, subst))
          val e1 = substExp(exp1, subst)
          MonoAst.MatchRule(p, g, e1)
      }
      MonoAst.Expr.Match(e, rs, tpe, eff, loc)

    case MonoAst.Expr.ExtMatch(exp, rules, tpe, eff, loc) =>
      val e = substExp(exp, subst)
      val rs = rules.map {
        case MonoAst.ExtMatchRule(pat, exp1, loc1) =>
          val p = substExtPattern(pat, subst)
          val e1 = substExp(exp1, subst)
          MonoAst.ExtMatchRule(p, e1, loc1)
      }
      MonoAst.Expr.ExtMatch(e, rs, tpe, eff, loc)

    case MonoAst.Expr.Cast(exp, tpe, eff, loc) =>
      val e = substExp(exp, subst)
      MonoAst.Expr.Cast(e, tpe, eff, loc)

    case MonoAst.Expr.TryCatch(exp, rules, tpe, eff, loc) =>
      val e = substExp(exp, subst)
      val rs = rules.map {
        case MonoAst.CatchRule(sym, clazz, exp1) =>
          val s = subst.getOrElse(sym, sym)
          val e1 = substExp(exp1, subst)
          MonoAst.CatchRule(s, clazz, e1)
      }
      MonoAst.Expr.TryCatch(e, rs, tpe, eff, loc)

    case MonoAst.Expr.RunWith(exp, effSymUse, rules, tpe, eff, loc) =>
      val e = substExp(exp, subst)
      val rs = rules.map {
        case MonoAst.HandlerRule(opSymUse, fparams, hexp) =>
          val fps = fparams.map(substFormalParam(_, subst))
          val he = substExp(hexp, subst)
          MonoAst.HandlerRule(opSymUse, fps, he)
      }
      MonoAst.Expr.RunWith(e, effSymUse, rs, tpe, eff, loc)

    case MonoAst.Expr.NewObject(_, _, _, _, _, _, _) => exp0

  }

  /**
    * Applies the given substitution `subst` to the given formal param `fparam0`.
    */
  private def substFormalParam(fparam0: MonoAst.FormalParam, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.FormalParam = fparam0 match {
    case MonoAst.FormalParam(sym, tpe, occur, loc) =>
      val s = subst.getOrElse(sym, sym)
      MonoAst.FormalParam(s, tpe, occur, loc)
  }

  /**
    * Applies the given substitution `subst` to the given pattern `pattern0`.
    */
  private def substPattern(pattern0: MonoAst.Pattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.Pattern = pattern0 match {
    case MonoAst.Pattern.Wild(tpe, loc) =>
      MonoAst.Pattern.Wild(tpe, loc)

    case MonoAst.Pattern.Var(sym, tpe, occur, loc) =>
      val s = subst.getOrElse(sym, sym)
      MonoAst.Pattern.Var(s, tpe, occur, loc)

    case MonoAst.Pattern.Cst(cst, tpe, loc) =>
      MonoAst.Pattern.Cst(cst, tpe, loc)

    case MonoAst.Pattern.Tag(symUse, pats, tpe, loc) =>
      val ps = pats.map(substPattern(_, subst))
      MonoAst.Pattern.Tag(symUse, ps, tpe, loc)

    case MonoAst.Pattern.Tuple(pats, tpe, loc) =>
      val ps = pats.map(substPattern(_, subst))
      MonoAst.Pattern.Tuple(ps, tpe, loc)

    case MonoAst.Pattern.Record(pats, pat, tpe, loc) =>
      val ps = pats.map(substRecordLabelPattern(_, subst))
      val p = substPattern(pat, subst)
      MonoAst.Pattern.Record(ps, p, tpe, loc)
  }

  /**
    * Applies the given substitution `subst` to the given record label pattern `pattern0`.
    */
  private def substRecordLabelPattern(pattern0: MonoAst.Pattern.Record.RecordLabelPattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.Pattern.Record.RecordLabelPattern = pattern0 match {
    case MonoAst.Pattern.Record.RecordLabelPattern(label, pat, tpe, loc) =>
      val p = substPattern(pat, subst)
      MonoAst.Pattern.Record.RecordLabelPattern(label, p, tpe, loc)
  }

  /**
    * Applies the given substitution `subst` to the given ext pattern `pattern0`.
    */
  private def substExtPattern(pattern0: MonoAst.ExtPattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.ExtPattern = pattern0 match {
    case MonoAst.ExtPattern.Default(loc) =>
      MonoAst.ExtPattern.Default(loc)

    case MonoAst.ExtPattern.Tag(label, pats, loc) =>
      val ps = pats.map(substVarOrWild(_, subst))
      MonoAst.ExtPattern.Tag(label, ps, loc)
  }

  /**
    * Applies the given substitution `subst` to the given ext tag pattern `pattern0`.
    */
  private def substVarOrWild(pattern0: MonoAst.ExtTagPattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): MonoAst.ExtTagPattern = pattern0 match {
    case MonoAst.ExtTagPattern.Wild(tpe, loc) =>
      MonoAst.ExtTagPattern.Wild(tpe, loc)

    case MonoAst.ExtTagPattern.Var(sym, tpe, occur, loc) =>
      val s = subst.getOrElse(sym, sym)
      MonoAst.ExtTagPattern.Var(s, tpe, occur, loc)

    case MonoAst.ExtTagPattern.Unit(tpe, loc) =>
      MonoAst.ExtTagPattern.Unit(tpe, loc)
  }

  /*
   * Methods for lowering provenance datalog expressions.
   */

  /**
    * Returns `t` from the Flix type `Vector[t]`.
    */
  private def unwrapVectorType(tpe: Type, loc: SourceLocation): Type = tpe match {
    case Type.Apply(Type.Cst(TypeConstructor.Vector, _), extType, _) => extType
    case t => throw InternalCompilerException(
      s"Expected Type.Apply(Type.Cst(TypeConstructor.Vector, _), _, _), but got $t",
      loc
    )
  }

  /**
    * Returns the pairs consisting of predicates and their term types from the extensible variant
    * type `tpe`.
    */
  private def predicatesOfExtVar(tpe: Type, loc: SourceLocation): List[(Name.Pred, List[Type])] = tpe match {
    case Type.Apply(Type.Cst(TypeConstructor.Extensible, _), tpe1, loc1) =>
      predicatesOfSchemaRow(tpe1, loc1)
    case t => throw InternalCompilerException(
      s"Expected Type.Apply(Type.Cst(TypeConstructor.Extensible, _), _, _), but got $t",
      loc
    )
  }

  /**
    * Returns the pairs consisting of predicates and their term types from the SchemaRow `row`.
    */
  private def predicatesOfSchemaRow(row: Type, loc: SourceLocation): List[(Name.Pred, List[Type])] = row match {
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SchemaRowExtend(pred), _), rel, loc2), tpe2, loc1) =>
      (pred, termTypesOfRelation(rel, loc2)) :: predicatesOfSchemaRow(tpe2, loc1)
    case Type.Var(_, _) => Nil
    case Type.SchemaRowEmpty => Nil
    case t => throw InternalCompilerException(s"Got unexpected $t", loc)
  }

  /**
    * Returns the types constituting a `Type.Relation`.
    */
  private def termTypesOfRelation(rel: Type, loc: SourceLocation): List[Type] = {
    def flattenApply(rel0: Type, loc0: SourceLocation): List[Type] = rel0 match {
      case Type.Cst(TypeConstructor.Relation(_), _) => Nil
      case Type.Apply(rest, t, loc1) => t :: flattenApply(rest, loc1)
      case _ if rel0.typeConstructor.contains(TypeConstructor.AnyType) => Nil
      // The type of the relation is undetermined, i.e. it is a free type variable that has been replaced by AnyType.
      // Since we have an AnyType we are free to treat it however we want. Here we decide to treat the relation as being nullary.
      case t => throw InternalCompilerException(s"Expected Type.Apply(_, _, _), but got $t", loc0)
    }

    flattenApply(rel, loc).reverse
  }

  /**
    * Returns the `MonoAst` lambda expression
    * {{{
    *   predSym: PredSym -> terms: Vector[Boxed] -> match predSym {
    *     case PredSym.PredSym(name, _) => match name {
    *       case "P1" => xvar P1(unbox(Vector.get(0, terms)), unbox(Vector.get(1, terms)), ...)
    *       case "P2" => xvar P2(unbox(Vector.get(0, terms)), unbox(Vector.get(1, terms)), ...)
    *       ...
    *     }
    *   }
    * }}}
    * where `P1, P2, ...` are in `preds` with their respective term types.
    */
  private def mkExtVarLambda(preds: List[(Name.Pred, List[Type])], tpe: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val predSymVar = Symbol.freshVarSym("predSym", BoundBy.FormalParam, loc)(RegionScope.Top, flix)
    val termsVar = Symbol.freshVarSym("terms", BoundBy.FormalParam, loc)(RegionScope.Top, flix)
    mkLambdaExp(predSymVar, Types.PredSym,
      mkLambdaExp(termsVar, Types.VectorOfBoxed,
        mkExtVarBody(preds, predSymVar, termsVar, tpe, loc),
        tpe, Type.Pure, loc
      ),
      Type.mkPureArrow(Types.VectorOfBoxed, tpe, loc), Type.Pure, loc
    )
  }

  /**
    * Returns the `MonoAst` lambda expression
    * {{{
    *   paramName -> exp
    * }}}
    * where `"paramName" == param.text` and `exp` has type `expType` and effect `eff`.
    */
  private def mkLambdaExp(param: Symbol.VarSym, paramTpe: Type, exp: MonoAst.Expr, expTpe: Type, eff: Type, loc: SourceLocation): MonoAst.Expr =
    MonoAst.Expr.Lambda(
      MonoAst.FormalParam(param, paramTpe, Occur.Unknown, loc),
      exp,
      Type.mkArrowWithEffect(paramTpe, eff, expTpe, loc),
      loc
    )

  /**
    * Returns the `MonoAst` match expression
    * {{{
    *   match predSym {
    *     case PredSym.PredSym(name, _) => match name {
    *       case "P1" => xvar P1(unbox(Vector.get(0, terms)), unbox(Vector.get(1, terms)), ...)
    *       case "P2" => xvar P2(unbox(Vector.get(0, terms)), unbox(Vector.get(1, terms)), ...)
    *       ...
    *     }
    *   }
    * }}}
    * where `P1, P2, ...` are in `preds` with their respective term types, `"predSym" == predSymVar.text`
    * and `"terms" == termsVar.text`.
    */
  private def mkExtVarBody(preds: List[(Name.Pred, List[Type])], predSymVar: Symbol.VarSym, termsVar: Symbol.VarSym, tpe: Type, loc: SourceLocation)(implicit ctx: Context, root: TypedAst.Root, flix: Flix): MonoAst.Expr = {
    val nameVar = Symbol.freshVarSym(Name.Ident("name", loc), BoundBy.Pattern)(RegionScope.Top, flix)
    MonoAst.Expr.Match(
      exp = MonoAst.Expr.Var(predSymVar, Types.PredSym, loc),
      rules = List(
        MonoAst.MatchRule(
          pat = MonoAst.Pattern.Tag(
            symUse = SymUse.CaseSymUse(findCaseSym(Enums.PredSym, "PredSym"), loc),
            pats = List(
              MonoAst.Pattern.Var(nameVar, Type.Str, Occur.Unknown, loc),
              MonoAst.Pattern.Wild(Type.Int64, loc)
            ),
            tpe = Types.PredSym, loc = loc
          ),
          guard = None,
          exp = MonoAst.Expr.Match(
            exp = MonoAst.Expr.Var(nameVar, Type.Str, loc),
            rules = preds.map {
              case (p, types) => mkProvenanceMatchRule(termsVar, tpe, p, types, loc)
            },
            tpe = tpe, eff = Type.Pure, loc = loc
          ),
        )
      ),
      tpe = tpe, eff = Type.Pure, loc
    )
  }

  /**
    * Returns the pattern match rule
    * {{{
    *   case "P" => xvar P(unbox(Vector.get(0, terms)), unbox(Vector.get(1, terms)), ...)
    * }}}
    * where `"P" == p.name`
    */
  private def mkProvenanceMatchRule(termsVar: Symbol.VarSym, tpe: Type, p: Name.Pred, types: List[Type], loc: SourceLocation)(implicit ctx: Context): MonoAst.MatchRule = {
    val termsExps = types.zipWithIndex.map {
      case (tpe1, i) => mkUnboxedTerm(termsVar, tpe1, i, loc)
    }
    MonoAst.MatchRule(
      pat = MonoAst.Pattern.Cst(Constant.Str(p.name), Type.Str, loc),
      guard = None,
      exp = MonoAst.Expr.ApplyAtomic(
        op = AtomicOp.ExtTag(Name.Label(p.name, loc)),
        exps = termsExps,
        tpe = tpe, eff = Type.Pure, loc = loc
      )
    )
  }

  /**
    * Returns the `MonoAst` expression
    * {{{
    *   unbox(Vector.get(i, terms))
    * }}}
    * where `"terms" == termsVar.text`.
    */
  private def mkUnboxedTerm(termsVar: Symbol.VarSym, tpe: Type, i: Int, loc: SourceLocation)(implicit ctx: Context): MonoAst.Expr = {
    val outerItpe = Type.mkPureUncurriedArrow(List(Types.Boxed), tpe, loc)
    val innerItpe = Type.mkPureUncurriedArrow(List(Type.Int32, Types.VectorOfBoxed), Types.Boxed, loc)
    MonoAst.Expr.ApplyDef(
      sym = lookup(Defs.Unbox, outerItpe),
      exps = List(
        MonoAst.Expr.ApplyDef(
          sym = lookup(Symbol.mkDefnSym(s"Vector.get"), innerItpe),
          exps = List(
            MonoAst.Expr.Cst(Constant.Int32(i), Type.Int32, loc),
            MonoAst.Expr.Var(termsVar, Types.VectorOfBoxed, loc)
          ),
          itpe = innerItpe,
          tpe = Types.Boxed, eff = Type.Pure, loc = loc
        )
      ),
      itpe = SolutionSpecialization.rewriteEnumStructType(outerItpe),
      tpe = SolutionSpecialization.rewriteEnumStructType(tpe), eff = Type.Pure, loc = loc
    )
  }

  /**
    * A local context threaded through `visitExp` to carry information from an
    * enclosing `NewObject` to nested `InvokeSuperMethod` expressions.
    *
    * @param sym     The symbol of the enclosing anonymous class.
    *                Set to `Some` when visiting a `NewObject` method body; `None` otherwise.
    *                Injected into `AtomicOp.InvokeSuperMethod` so the backend can generate
    *                the `CHECKCAST` and `INVOKEVIRTUAL super$methodName` instructions.
    * @param thisRef A `Var` expression referencing the `_this` parameter (the first formal
    *                parameter of the JvmMethod). Prepended to `InvokeSuperMethod` arguments
    *                so the backend receives the receiver object as the first expression.
    */
  private case class LocalContext(sym: Option[Symbol.AnonClassSym], thisRef: Option[MonoAst.Expr])

  private object LocalContext {
    val empty: LocalContext = LocalContext(None, None)
  }

}
