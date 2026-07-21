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
import ca.uwaterloo.flix.language.ast.{Kind, Name, SourceLocation, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.ast.TypedAst.{Expr, FormalParam, MatchRule, Predicate}
import ca.uwaterloo.flix.language.ast.ops.TypedAstOps
import ca.uwaterloo.flix.language.ast.shared.Denotation
import ca.uwaterloo.flix.language.phase.monomorph.Symbols
import ca.uwaterloo.flix.language.phase.monomorph.Symbols.{Defs, Enums, Types}
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

/**
  * Constraint generation for constraint-based monomorphization: emits `Flow` constraints
  * describing how concrete types propagate through the program, for [[ConstraintSolver]] to solve.
  */
object ConstraintCollection {

  /**
    * Generation context.
    *
    * @param currentDecl the decl which we are currently traversing
    * @param tparamEnv maps the current def's type parameters to their indices
    * @param root the typed AST root (needed to resolve ground associated types)
    * @param flix the Flix context (needed by TypeReduction2)
    */
  case class Context(
    currentDecl: MonoVar,
    tparamEnv: Map[Symbol.KindedTypeVarSym, Int],
    root: TypedAst.Root,
    flix: Flix
  )

  /**
    * Generates specialization constraints for every top-level definition, enum, and trait instance.
    */
  def generate(root: TypedAst.Root)(implicit flix: Flix): Set[Flow] = flix.phase("ConstraintCollection") {
    val fromDefs = ParOps.parMap(root.defs.values) { defn =>
      flix.profile(defn.sym, defn.loc) {
        val tparamEnv = defn.spec.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
        implicit val ctx: Context = Context(MonoVar.Def(defn.sym), tparamEnv, root, flix)
        visitDef(defn, Nil)
      }
    }.flatten.toSet

    val fromEnums = ParOps.parMap(root.enums.values) { enm =>
      val tparamEnv = enm.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MonoVar.Enum(enm.sym), tparamEnv, root, flix)
      visitEnum(enm, Nil)
    }.flatten.toSet

    val fromInstances = ParOps.parMap(root.instances.values) { inst =>
      val instTparamEnv = inst.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      inst.defs.flatMap { instDef =>
        // Add spec.tparams that are NOT already covered by inst.tparams (e.g. a, b, ef in
        // Applicative[Option].ap). Generic instances (e.g. Eq[(a, b)]) duplicate inst.tparams
        // in spec.tparams, so filtering avoids overwriting the correct instTparam indices.
        val offset = inst.tparams.length
        val newSpecTparams = instDef.spec.tparams.filterNot(tp => instTparamEnv.contains(tp.sym))
        val specTparamEnv = newSpecTparams.zipWithIndex.map { case (tp, j) => tp.sym -> (offset + j) }.toMap
        flix.profile(instDef.sym, instDef.loc) {
          implicit val ctx: Context = Context(MonoVar.Def(instDef.sym), instTparamEnv ++ specTparamEnv, root, flix)
          visitDef(instDef, Nil)
        }
      }
    }.flatten.toSet

    val fromRestrictableEnums = ParOps.parMap(root.restrictableEnums.values) { enm =>
      val tparamEnv = (enm.index :: enm.tparams).zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MonoVar.RestrictableEnum(enm.sym), tparamEnv, root, flix)
      visitRestrictableEnum(enm, Nil)
    }.flatten.toSet

    val fromStructs = ParOps.parMap(root.structs.values) { struct =>
      val tparamEnv = struct.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MonoVar.Struct(struct.sym), tparamEnv, root, flix)
      visitStruct(struct, Nil)
    }.flatten.toSet

    // Visits default trait-impl bodies (root.sigs with exp.isDefined) so dispatched sigs propagate.
    // fromSigs/fromEffects synthesize a DefnSym so their own tparams  classify as Param, not
    // wrongly-ground Const. (Same is true for fromEffects)
    val fromSigs = ParOps.parMap(root.sigs.values.filter(_.exp.isDefined)) { sig =>
      // traitTparam (e.g. `t` in `Foldable[t]`) isn't in sig.spec.tparams but is free in the
      // default impl body — prepended so index 0 matches ConstraintSolver.resolveSig's tuple
      // layout: [traitType, ...sig-own args].
      val trt = root.traits(sig.sym.trt)
      val traitTparam = trt.tparam
      val allTparams = traitTparam :: sig.spec.tparams
      val tparamEnv = allTparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      val ns = sig.sym.trt.namespace :+ sig.sym.trt.name
      val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
      flix.profile(defnSym, sig.sym.loc) {
        implicit val ctx: Context = Context(MonoVar.Def(defnSym), tparamEnv, root, flix)
        sig.exp.map(e => visitExp(e, Nil)).getOrElse(Nil)
      }
    }.flatten.toSet

    val fromEffects = ParOps.parMap(root.effects.values.flatMap(_.ops)) { op =>
      val tparamEnv = op.spec.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      val defnSym = new Symbol.DefnSym(None, op.sym.namespace, op.sym.name, op.sym.loc)
      implicit val ctx: Context = Context(MonoVar.Def(defnSym), tparamEnv, root, flix)
      val acc1 = op.spec.fparams.foldLeft(List.empty[Flow]) { case (a, FormalParam(_, tpe, _, _, _)) => visitType(tpe, a) }
      visitType(op.spec.retTpe, acc1)
    }.flatten.toSet

    fromDefs ++ fromEnums ++ fromInstances ++ fromRestrictableEnums ++ fromStructs ++ fromSigs ++ fromEffects
  }(MonomorphDebug.DebugFlows)

  // Performance: every visit* function threads an immutable `acc: List[Flow]` accumulator (cons,
  // no per-node Set allocation). Duplicate flows are fine — dedup happens once, in `generate`'s
  // final `.toSet`.

  /**
    * Emits flow constraints for enum type applications occurring in `tpe`.
    */
  private def visitType(tpe0: Type, acc: List[Flow])(implicit ctx: Context): List[Flow] = Type.eraseAliases(tpe0) match {
    // Deep alias erasure above because flattenApply/.typeArguments below don't check for Type.Alias
    case at @ Type.AssocType(_, arg, _, _) =>
      // If the associated type is ground, resolve it and continue; otherwise recurse into arg.
      if (at.typeVars.isEmpty) visitType(MonomorphCanon.reduceAssocType(at)(ctx.root, ctx.flix), acc)
      else visitType(arg, acc)
    case _: Type.BaseType
         | Type.Var(_, _)
         | Type.Cst(_, _) => acc
    case app @ Type.Apply(_, _, _) =>
      val (head, args) = MonomorphHelpers.flattenApply(app)
      val acc1 = args.foldLeft(acc)((a, t) => visitType(t, a))
      val mvarOpt = head match {
        case Type.Cst(TypeConstructor.Enum(sym, _), _)             => Some(MonoVar.Enum(sym))
        case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) => Some(MonoVar.RestrictableEnum(sym))
        case Type.Cst(TypeConstructor.Struct(sym, _), _)           => Some(MonoVar.Struct(sym))
        case _                                                     => None
      }
      mvarOpt match {
        case Some(mvar) => Flow(args.map(t => typeToMonoArg(t)), mvar) :: acc1
        case None       => acc1
      }
  }

  /**
    * Emits flow constraints for all case field types in `enumDecl`.
    */
  private def visitEnum(enumDecl: TypedAst.Enum, acc: List[Flow])(implicit ctx: Context): List[Flow] =
    enumDecl.cases.values.foldLeft(acc) { (a, cas) => cas.tpes.foldLeft(a)((a2, t) => visitType(t, a2)) }

  /**
    * Emits flow constraints for all case field types in `restrictableEnumDecl`.
    */
  private def visitRestrictableEnum(restrictableEnumDecl: TypedAst.RestrictableEnum, acc: List[Flow])(implicit ctx: Context): List[Flow] =
    restrictableEnumDecl.cases.values.foldLeft(acc) { (a, cas) => cas.tpes.foldLeft(a)((a2, t) => visitType(t, a2)) }

  /**
    * Emits flow constraints for all field types in `structDecl`.
    */
  private def visitStruct(structDecl: TypedAst.Struct, acc: List[Flow])(implicit ctx: Context): List[Flow] =
    structDecl.fields.values.foldLeft(acc) { (a, field) => visitType(field.tpe, a) }

  /**
    * Emits flow constraints for the formal parameter types, return type, and body of `defn`.
    */
  private def visitDef(defn: TypedAst.Def, acc: List[Flow])(implicit ctx: Context): List[Flow] = {
    val acc1 = defn.spec.fparams.foldLeft(acc) { case (a, FormalParam(_, tpe, _, _, _)) => visitType(tpe, a) }
    val acc2 = visitType(defn.spec.retTpe, acc1)
    val acc3 = visitExp(defn.exp, acc2)
    entryPointHandlerFlows(defn, acc3)
  }

  /**
    * Emits flow constraints for the default-handler calls that
    * `SolutionLowering.wrapDefWithDefaultHandlers` synthesizes around entry points (main, `@Test`,
    * `@Export`).
    *
    * Mirrors `SolutionLowering.wrapInHandler`: each required default handler is applied in
    * sequence, instantiated at `(Unit -> retTpe \ ef) -> retTpe \ ((ef - handledEff) + IO)`, where
    * `ef` starts as `defn.spec.eff` and is threaded through the fold exactly as the lowering does.
    */
  private def entryPointHandlerFlows(defn: TypedAst.Def, acc: List[Flow])(implicit ctx: Context): List[Flow] = {
    if (!TypedAstOps.isEntryPoint(defn)(ctx.root)) acc
    else {
      val loc = defn.spec.eff.loc
      val defEffects = MonomorphCanon.evalEffect(defn.spec.eff)
      val requiredHandlers = ctx.root.defaultHandlers.filter(h => defEffects.contains(h.handledSym))
      var eff = defn.spec.eff
      requiredHandlers.foldLeft(acc) { (a, handler) =>
        // Handler signature is `pub def h(f: Unit -> a \ ef): a \ ...` with tparams inferred
        // in order of first occurrence: [ef, a] (the effect var in the arrow, then the result type).
        val flow = Flow(
          List(typeToMonoArg(eff), typeToMonoArg(defn.spec.retTpe)),
          MonoVar.Def(handler.handlerSym)
        )
        // Canonicalized to match SolutionLowering.wrapInHandler, which threads the canonical (not
        // raw formula) effect into the next handler wrap via this same MonomorphCanon.canonicalEffect call.
        eff = MonomorphCanon.canonicalEffect(Type.mkUnion(Type.mkDifference(eff, handler.handledEff, loc), Type.IO, loc))
        flow :: a
      }
    }
  }

  /**
    * Emits flow constraints for all call sites and enum usages in `exp`. Datalog and channel
    * nodes additionally emit constraints for the stdlib calls [[SolutionLowering]] will
    * synthesize for them.
    */
  private def visitExp(exp: Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = exp match {
    case Expr.Cst(_, _, _) => acc
    case Expr.Var(_, _, _) => acc
    case Expr.Hole(_, _, _, _, _) => acc

    case Expr.ApplyDef(symUse, exps, targs, _, _, _, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(targs.map(typeToMonoArg(_)), MonoVar.Def(symUse.sym)) :: acc1

    case Expr.ApplySig(symUse, exps, targ, targs, _, _, _, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow((targ :: targs).map(typeToMonoArg(_)), MonoVar.Sig(symUse.sym)) :: acc1

    case Expr.ApplyOp(_, exps, _, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.ApplyClo(exp1, exp2, _, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.Unary(_, exp, _, _, _) => visitExp(exp, acc)

    case Expr.Binary(_, exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.Let(_, exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.Lambda(_, exp, _, _) => visitExp(exp, acc)

    case Expr.IfThenElse(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp3, visitExp(exp2, visitExp(exp1, acc)))

    case Expr.Stm(exps, exp, _, _, _) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      visitExp(exp, acc1)

    case Expr.Discard(exp, _, _) => visitExp(exp, acc)

    case Expr.Region(_, _, exp, _, _, _) => visitExp(exp, acc)

    case Expr.Use(_, _, exp, _) => visitExp(exp, acc)

    // Unlike the paper we don't annotate the match with the scrutinee enum type, because Flix
    // match rules do not carry a type-parameter annotation (as they do in LangPoly).
    case Expr.Match(exp, rules, _, _, _) =>
      val acc1 = visitExp(exp, acc)
      rules.foldLeft(acc1) {
        case (a, MatchRule(pat, guardOpt, body, _)) =>
          val a0 = visitPat(pat, a)
          val a1 = guardOpt.foldLeft(a0)((a2, g) => visitExp(g, a2))
          visitExp(body, a1)
      }

    // Tag and RestrictableTag are handled identically: getEnumMonoVarAndTypeArgs dispatches on the
    // type itself, and the solver handles both resulting mvar kinds.
    case Expr.Tag(_, exps, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMonoVarAndTypeArgs(tpe, loc)
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(tpArgs.map(typeToMonoArg(_)), mvar) :: acc1

    case Expr.RestrictableTag(_, exps, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMonoVarAndTypeArgs(tpe, loc)
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(tpArgs.map(typeToMonoArg(_)), mvar) :: acc1

    case Expr.RestrictableChoose(_, exp, rules, _, _, _) =>
      val acc1 = visitExp(exp, acc)
      rules.foldLeft(acc1)((a, r) => visitExp(r.exp, a))

    case Expr.ExtMatch(exp, rules, _, _, _) =>
      val acc1 = visitExp(exp, acc)
      rules.foldLeft(acc1)((a, r) => visitExp(r.exp, a))

    case Expr.ExtTag(_, exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.OpenAs(_, exp, _, _) => visitExp(exp, acc)

    case Expr.Tuple(exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.LocalDef(_, bnd, _, exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, visitType(bnd.tpe, acc)))

    case Expr.ApplyLocalDef(_, exps, _, _, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.HoleWithExp(exp, _, _, _, _) => visitExp(exp, acc)

    case Expr.RecordSelect(exp, _, _, _, _) => visitExp(exp, acc)

    case Expr.RecordExtend(_, exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.RecordRestrict(_, exp, _, _, _) => visitExp(exp, acc)

    case Expr.ArrayLit(exps, exp, _, _, _) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      visitExp(exp, acc1)

    case Expr.ArrayNew(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp3, visitExp(exp2, visitExp(exp1, acc)))

    case Expr.ArrayLoad(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.ArrayLength(exp, _, _) => visitExp(exp, acc)

    case Expr.ArrayStore(exp1, exp2, exp3, _, _) =>
      visitExp(exp3, visitExp(exp2, visitExp(exp1, acc)))

    case Expr.VectorLit(exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.VectorLoad(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.VectorLength(exp, _) => visitExp(exp, acc)

    // Mirrors Expr.Tag: a construction site's concrete type args must seed the solver;
    // visitType alone only captures the declaration's own field-type structure.
    case Expr.StructNew(_, fields, region, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMonoVarAndTypeArgs(tpe, loc)
      val acc1 = fields.foldLeft(acc) { case (a, (_, e)) => visitExp(e, a) }
      val acc2 = region.foldLeft(acc1)((a, r) => visitExp(r, a))
      Flow(tpArgs.map(typeToMonoArg(_)), mvar) :: acc2

    case Expr.StructGet(exp, _, _, _, _) => visitExp(exp, acc)

    case Expr.StructPut(exp1, _, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.Lazy(exp, _, _) => visitExp(exp, acc)

    case Expr.Force(exp, _, _, _) => visitExp(exp, acc)

    case Expr.Ascribe(exp, _, _, _, _, _) => visitExp(exp, acc)

    case Expr.InstanceOf(exp, _, _) => visitExp(exp, acc)

    case Expr.CheckedCast(_, exp, _, _, _) => visitExp(exp, acc)

    case Expr.UncheckedCast(exp, _, _, _, _, _) => visitExp(exp, acc)

    case Expr.Unsafe(exp, _, _, _, _, _) => visitExp(exp, acc)

    case Expr.TryCatch(exp, rules, _, _, _) =>
      val acc1 = visitExp(exp, acc)
      rules.foldLeft(acc1)((a, r) => visitExp(r.exp, a))

    case Expr.Throw(exp, _, _, _) => visitExp(exp, acc)

    case Expr.Handler(_, rules, _, _, _, _, _) =>
      rules.foldLeft(acc)((a, r) => visitExp(r.exp, a))

    case Expr.RunWith(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.Spawn(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    // Lowering synthesizes Channel.get/put/newChannel calls for each non-last fragment.
    case Expr.ParYield(frags, exp, _, _, loc) =>
      val acc1 = frags.foldLeft(acc)((a, f) => visitExp(f.exp, visitPat(f.pat, a)))
      val acc2 = visitExp(exp, acc1)
      frags.init.foldLeft(acc2) { (a, frag) =>
        val elmType = frag.exp.tpe
        val elmArg = typeToMonoArg(lowerChannelType(elmType))
        Flow(List(elmArg), MonoVar.Def(Defs.ChannelNew)) ::
          Flow(List(elmArg), MonoVar.Def(Defs.ChannelPut)) ::
          Flow(List(elmArg), MonoVar.Def(Defs.ChannelGet)) :: a
      }

    case Expr.InvokeConstructor(_, exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.InvokeSuperConstructor(_, exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.InvokeMethod(_, exp, exps, _, _, _) =>
      val acc1 = visitExp(exp, acc)
      exps.foldLeft(acc1)((a, e) => visitExp(e, a))

    case Expr.InvokeSuperMethod(_, exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.InvokeStaticMethod(_, exps, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    case Expr.GetField(_, exp, _, _, _) => visitExp(exp, acc)

    case Expr.PutField(_, exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.GetStaticField(_, _, _, _) => acc

    case Expr.PutStaticField(_, exp, _, _, _) => visitExp(exp, acc)

    case Expr.NewObject(_, _, _, _, constructors, methods, _) =>
      val acc1 = constructors.foldLeft(acc)((a, c) => visitExp(c.exp, a))
      methods.foldLeft(acc1)((a, m) => visitExp(m.exp, a))

    // Channel nodes recurse into sub-expressions AND emit flows for the @LoweringTargetChannel
    // defs that Lowering will synthesize: GetChannel → Channel.get, PutChannel → Channel.put,
    // NewChannel → Channel.newChannelTuple.
    case Expr.GetChannel(exp, tpe, _, loc) =>
      val acc1 = visitExp(exp, acc)
      Flow(List(typeToMonoArg(lowerChannelType(tpe))), MonoVar.Def(Defs.ChannelGet)) :: acc1

    case Expr.PutChannel(exp1, exp2, _, _, loc) =>
      val acc1 = visitExp(exp2, visitExp(exp1, acc))
      Flow(List(typeToMonoArg(lowerChannelType(exp2.tpe))), MonoVar.Def(Defs.ChannelPut)) :: acc1

    case Expr.NewChannel(exp, tpe, _, loc) =>
      val elmType = extractChannelElm(tpe)
      val acc1 = visitExp(exp, acc)
      Flow(List(typeToMonoArg(lowerChannelType(elmType))), MonoVar.Def(Defs.ChannelNewTuple)) :: acc1

    // Lowering synthesizes, per rule, Channel.mpmcAdmin and Channel.unsafeGetAndUnlock calls
    // (not Channel.get), plus one fixed List[ChannelMpmcAdmin] built directly via mkTag/mkList,
    // whose instantiation must be predicted here too.
    case Expr.SelectChannel(rules, default, _, _, loc) =>
      val acc1 = rules.foldLeft(acc) { (a, r) =>
        val elmType = r.chan.tpe match {
          case Type.Apply(Type.Apply(_, e, _), _, _) => e  // Mpmc[T, rc] → T
          case Type.Apply(_, e, _)                    => e  // Sender[T] / Receiver[T] → T
          case t                                      => t
        }
        val elmArg = typeToMonoArg(lowerChannelType(elmType))
        val a1 = visitExp(r.exp, visitExp(r.chan, a))
        Flow(List(elmArg), MonoVar.Def(Defs.ChannelUnsafeGetAndUnlock)) ::
          Flow(List(elmArg), MonoVar.Def(Defs.ChannelMpmcAdmin)) :: a1
      }
      val acc2 = default.foldLeft(acc1)((a, d) => visitExp(d, a))
      Flow(List(typeToMonoArg(Types.ChannelMpmcAdmin)), MonoVar.Enum(Enums.FList)) :: acc2

    // Datalog fixpoint nodes recurse into sub-expressions AND emit flows for every
    // Box/Unbox/liftN/lattice/Facts/ProjectInto/ProvenanceOf call SolutionLowering will
    // synthesize, mirroring the TypedAst structure lowering itself inspects.
    case Expr.FixpointConstraintSet(cs, _, _) =>
      cs.foldLeft(acc) { (a0, c) =>
        val cparams0 = c.cparams
        val a1 = c.head match {
          case Predicate.Head.Atom(_, den, terms, _, loc) =>
            val h1 = terms.foldLeft(a0)((x, t) => visitExp(t, x))
            val h2 = terms.foldLeft(h1)((x, t) => headTermFlows(cparams0, t, x))
            latticeFlows(den, terms.lastOption.map(_.tpe), loc, h2)
        }
        c.body.foldLeft(a1) {
          case (x, Predicate.Body.Guard(e, _)) =>
            guardLiftFlow(cparams0, e, visitExp(e, x))
          case (x, Predicate.Body.Functional(outBnds, e, loc)) =>
            functionalLiftFlow(cparams0, outBnds.length, e, loc) :: visitExp(e, x)
          case (x, Predicate.Body.Atom(_, den, _, _, terms, _, loc)) =>
            latticeFlows(den, terms.lastOption.map(_.tpe), loc, bodyAtomTermFlows(cparams0, terms, x))
        }
      }

    // Lowering builds a List[PredSym] directly via mkTag/mkList (bypassing the ordinary rewrite
    // path), so its instantiation must be predicted here.
    case Expr.FixpointLambda(_, exp, _, _, loc) =>
      val acc1 = visitExp(exp, acc)
      Flow(List(typeToMonoArg(Types.PredSym)), MonoVar.Enum(Enums.FList)) :: acc1

    case Expr.FixpointMerge(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.FixpointSolveWithProject(exps, _, _, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    // Lowering synthesizes Fixpoint3.Solver.injectIntoN(p, ts), generic over the container
    // constructor and the tuple's component types.
    case Expr.FixpointInjectInto(exps, _, _, _, loc) =>
      exps.foldLeft(acc) { (a, e) =>
        val (tycon, argTypes) = Type.eraseAliases(e.tpe) match {
          case Type.Apply(tc, innerType, _) =>
            innerType.typeConstructor match {
              case Some(TypeConstructor.Tuple(_)) => (tc, innerType.typeArguments)
              case Some(TypeConstructor.Unit)     => (tc, Nil)
              case _                              => (tc, List(innerType))
            }
          case t => throw InternalCompilerException(s"Unexpected non-foldable type: '$t'.", loc)
        }
        val flowArgs = (tycon :: argTypes).map(typeToMonoArg(_))
        val a1 = visitExp(e, a)
        Flow(flowArgs, MonoVar.Def(Defs.ProjectInto(argTypes.length))) :: a1
      }

    // Lowering synthesizes Fixpoint3.Solver.factsN(p, d), generic over the N selected terms'
    // types. Facts(arity)'s flow args must come from the resolved result type `tpe0`, NOT from
    // `selects`' own term types, which may still carry locally-scoped type vars.
    case Expr.FixpointQueryWithSelect(exps, queryExp, selects, from, where, _, tpe0, _, loc) =>
      val arity = selects.length
      val innerTpe = unwrapVectorType(tpe0, loc)
      val argTypes = if (arity <= 1) List(innerTpe) else innerTpe.typeArguments
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      val acc2 = visitExp(queryExp, acc1)
      val acc3 = selects.foldLeft(acc2)((a, e) => visitExp(e, a))
      val acc4 = from.foldLeft(acc3) {
        case (a, Predicate.Body.Guard(e, _))         => visitExp(e, a)
        case (a, Predicate.Body.Functional(_, e, _)) => visitExp(e, a)
        case (a, _: Predicate.Body.Atom)             => a
      }
      val acc5 = where.foldLeft(acc4)((a, e) => visitExp(e, a))
      Flow(argTypes.map(typeToMonoArg(_)), MonoVar.Def(Defs.Facts(arity))) :: acc5

    // Lowering boxes every goal term, unboxes every term type the extensible-variant result can
    // carry, and calls Solver.provenanceOf and Vector.get at a fixed Boxed type.
    case Expr.FixpointQueryWithProvenance(exps, select, _, tpe0, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      val acc2 = select match {
        case Predicate.Head.Atom(_, _, terms, _, _) =>
          val s1 = terms.foldLeft(acc1)((a, t) => visitExp(t, a))
          terms.foldLeft(s1)((a, t) => boxFlow(t.tpe) :: a)
      }
      val extVarType = unwrapVectorType(tpe0, loc)
      val acc3 = predicatesOfExtVar(extVarType, loc).flatMap(_._2).foldLeft(acc2) { (a, t) =>
        Flow(List(typeToMonoArg(t)), MonoVar.Def(Defs.Unbox)) :: a
      }
      Flow(List(typeToMonoArg(Types.Boxed)), MonoVar.Def(Defs.VectorGet)) ::
        Flow(List(typeToMonoArg(extVarType)), MonoVar.Def(Defs.ProvenanceOf)) :: acc3

    case Expr.Error(_, _, _) => acc
  }

  /**
    * Emits flow constraints for enum instantiations mentioned by patterns.
    *
    * ⚠️ IMPORTANT — DELIBERATE `AnyType` SPECIALIZATION. A pattern can mention an enum
    * instantiation that no expression ever constructs, e.g.
    * `match None { case Some(Ok(_)) => ... }`: no `Result` value exists anywhere, so its tparams
    * are stray and default to `AnyType`. Without these flows the solver never proposes such
    * tuples and `SolutionSpecialization.lookupCaseSym` would miss on the pattern's lookup.
    * We deliberately specialize these instantiations AT `AnyType` like any other tuple: the
    * resulting declarations are dead (no value of `AnyType` can exist; fields erase to `Object`),
    * and in exchange every specialization lookup stays strict — a table miss is ALWAYS a
    * compiler bug ("Solver gap"), never silently tolerated. Do NOT reintroduce a
    * keep-the-original-sym fallback here or in the lookups. And NEVER let a defaulted `AnyType`
    * reach `Fixpoint.Boxable`'s box/unbox: their unchecked casts turn an imprecise type into a
    * silently wrong runtime value instead of dead code (see `termTypesOfRelation`).
    */
  private def visitPat(pat0: TypedAst.Pattern, acc: List[Flow])(implicit ctx: Context): List[Flow] = pat0 match {
    case TypedAst.Pattern.Tag(_, pats, tpe, loc) =>
      val (mvar, tpArgs) = getEnumMonoVarAndTypeArgs(tpe, loc)
      val acc1 = pats.foldLeft(acc)((a, p) => visitPat(p, a))
      Flow(tpArgs.map(typeToMonoArg(_)), mvar) :: acc1
    case TypedAst.Pattern.Tuple(elms, _, _) =>
      elms.toList.foldLeft(acc)((a, p) => visitPat(p, a))
    case TypedAst.Pattern.Record(pats, pat, _, _) =>
      val acc1 = pats.foldLeft(acc)((a, lp) => visitPat(lp.pat, a))
      visitPat(pat, acc1)
    case TypedAst.Pattern.Wild(_, _) | TypedAst.Pattern.Var(_, _, _) | TypedAst.Pattern.Cst(_, _, _) | TypedAst.Pattern.Error(_, _) =>
      acc
  }

  /** A flow for `Fixpoint3.Boxable.box` at type `tpe` — mirrors `SolutionLowering.box`. */
  private def boxFlow(tpe: Type)(implicit ctx: Context): Flow =
    Flow(List(typeToMonoArg(tpe)), MonoVar.Def(Defs.Box))

  /**
    * Flows for a head term — mirrors `SolutionLowering.lowerHeadTerm`'s cases 1.2/2/3: a
    * lexically-bound Var, or a non-Var term with no quantified free vars, is boxed; a non-Var
    * term WITH quantified free vars is lifted via `lift{arity}` instead (never both). A
    * quantified Var itself (case 1.1) needs neither flow — it carries no runtime value of its own.
    */
  private def headTermFlows(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = exp0 match {
    case Expr.Var(sym, tpe, _) =>
      if (MonomorphHelpers.isQuantifiedVar(sym, cparams0)) acc else boxFlow(tpe) :: acc
    case _ =>
      val fvs = MonomorphHelpers.quantifiedVars(cparams0, exp0)
      if (fvs.isEmpty) boxFlow(exp0.tpe) :: acc
      else Flow((fvs.map(_._2) :+ exp0.tpe).map(typeToMonoArg(_)), MonoVar.Def(Defs.Lift(fvs.length))) :: acc
  }

  /**
    * Flows for a body atom's terms — mirrors `SolutionLowering.lowerBodyTerm`: `Wild` and a
    * quantified `Var` need nothing; a non-quantified `Var` or any `Cst` is boxed.
    */
  private def bodyAtomTermFlows(cparams0: List[TypedAst.ConstraintParam], terms: List[TypedAst.Pattern], acc: List[Flow])(implicit ctx: Context): List[Flow] =
    terms.foldLeft(acc) {
      case (a, TypedAst.Pattern.Wild(_, _)) => a
      case (a, TypedAst.Pattern.Var(bnd, tpe, _)) =>
        if (MonomorphHelpers.isQuantifiedVar(bnd.sym, cparams0)) a else boxFlow(tpe) :: a
      case (a, TypedAst.Pattern.Cst(_, tpe, _)) => boxFlow(tpe) :: a
      case (a, _) => a
    }

  /**
    * A flow for `lift{arity}b`, mirroring `SolutionLowering.mkGuard`. An arity-0 guard is
    * lowered to a plain closure with no lift call at all (`Guard0` — there is no `lift0b`), so
    * nothing is emitted in that case.
    */
  private def guardLiftFlow(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = {
    val fvs = MonomorphHelpers.quantifiedVars(cparams0, exp0)
    if (fvs.isEmpty) acc
    else Flow(fvs.map(kv => typeToMonoArg(kv._2)), MonoVar.Def(Defs.LiftB(fvs.length))) :: acc
  }

  /**
    * A flow for `lift{inArity}X{outArity}`, mirroring `SolutionLowering.mkFunctional`. Whether
    * `exp0.tpe`'s inner type decomposes into `o1,...,om` or is used whole as the single `o1`
    * depends on `outArity` (the *count* of out-vars) — NOT on whether that inner type happens to
    * look like a tuple: an outArity-1 functional can itself bind a single tuple-typed value (as
    * `lift0X1(f: Vector[(o1)])`'s signature — `(o1)` is just `o1` parenthesized, never a real
    * tuple type), so a structural "is this a Tuple" check would wrongly decompose it.
    */
  private def functionalLiftFlow(cparams0: List[TypedAst.ConstraintParam], outArity: Int, exp0: TypedAst.Expr, loc: SourceLocation)(implicit ctx: Context): Flow = {
    val inVars = MonomorphHelpers.quantifiedVars(cparams0, exp0)
    val inner = Type.eraseAliases(exp0.tpe) match {
      case Type.Apply(Type.Cst(TypeConstructor.Vector, _), t, _) => t
      case t => throw InternalCompilerException(s"Expected Vector[_], but got $t", loc)
    }
    val outTypes = if (outArity <= 1) List(inner) else inner.typeArguments
    Flow((inVars.map(_._2) ++ outTypes).map(typeToMonoArg(_)), MonoVar.Def(Defs.LiftXM(inVars.length, outArity)))
  }

  /**
    * Flows for `Fixpoint3.Ast.Shared.lattice`/`box`/`Denotation`, mirroring
    * `SolutionLowering.mkDenotation`. The `Relational` case constructs a `Denotation[Boxed]`
    * directly via `mkTag` (bypassing the ordinary rewrite path), so its enum-construction flow
    * must be predicted here or `enumTable` never gets an entry for it.
    */
  private def latticeFlows(den: Denotation, lastTermType: Option[Type], loc: SourceLocation, acc: List[Flow])(implicit ctx: Context): List[Flow] = den match {
    case Denotation.Relational =>
      Flow(List(typeToMonoArg(Types.Boxed)), MonoVar.Enum(Enums.Denotation)) :: acc
    case Denotation.Latticenal =>
      val tpe = lastTermType.getOrElse(throw InternalCompilerException("Unexpected nullary lattice predicate.", loc))
      Flow(List(typeToMonoArg(tpe)), MonoVar.Def(Defs.Lattice)) ::
        Flow(List(typeToMonoArg(tpe)), MonoVar.Def(Defs.LatticeBox)) :: acc
  }

  /** Returns `t` from `Vector[t]` — mirrors `SolutionLowering.unwrapVectorType`. */
  private def unwrapVectorType(tpe: Type, loc: SourceLocation): Type = Type.eraseAliases(tpe) match {
    case Type.Apply(Type.Cst(TypeConstructor.Vector, _), extType, _) => extType
    case t => throw InternalCompilerException(s"Expected Type.Apply(Type.Cst(TypeConstructor.Vector, _), _, _), but got $t", loc)
  }

  /** Mirrors `SolutionLowering.predicatesOfExtVar`. */
  private def predicatesOfExtVar(tpe: Type, loc: SourceLocation): List[(Name.Pred, List[Type])] = Type.eraseAliases(tpe) match {
    case Type.Apply(Type.Cst(TypeConstructor.Extensible, _), tpe1, loc1) => predicatesOfSchemaRow(tpe1, loc1)
    case t => throw InternalCompilerException(s"Expected Type.Apply(Type.Cst(TypeConstructor.Extensible, _), _, _), but got $t", loc)
  }

  /** Mirrors `SolutionLowering.predicatesOfSchemaRow`. */
  private def predicatesOfSchemaRow(row: Type, loc: SourceLocation): List[(Name.Pred, List[Type])] = row match {
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SchemaRowExtend(pred), _), rel, loc2), tpe2, loc1) =>
      (pred, termTypesOfRelation(rel, loc2)) :: predicatesOfSchemaRow(tpe2, loc1)
    case Type.Var(_, _) | Type.SchemaRowEmpty => Nil
    case t => throw InternalCompilerException(s"Got unexpected $t", loc)
  }

  /**
    * Mirrors `SolutionLowering.termTypesOfRelation`, with one addition: this file runs pre-solve,
    * where a relation of an under-constrained provenance predicate can still be a bare
    * `Type.Var`. Such a var is skipped (not defaulted — that would be unsound for Box/Unbox/liftN
    * flows, and a genuine miss still surfaces as a clean solver gap downstream).
    */
  private def termTypesOfRelation(rel: Type, loc: SourceLocation): List[Type] = {
    def flattenApply(rel0: Type, loc0: SourceLocation): List[Type] = rel0 match {
      case Type.Cst(TypeConstructor.Relation(_), _) => Nil
      case Type.Apply(rest, t, loc1) => t :: flattenApply(rest, loc1)
      case _ if rel0.typeConstructor.contains(TypeConstructor.AnyType) => Nil
      case Type.Var(_, _) => Nil
      case t => throw InternalCompilerException(s"Expected Type.Apply(_, _, _), but got $t", loc0)
    }
    flattenApply(rel, loc).reverse
  }


  /**
    * Extracts the element type T for Channel.newChannelTuple.
    * NewChannel.tpe may be (Sender[T], Receiver[T]) where Sender/Receiver are single-arg aliases,
    * or (Mpmc[T, rc], Mpmc[T, rc]) where Mpmc is a two-arg type constructor.
    * In the single-channel case it may be Mpmc[T, rc] or Sender[T].
    */
  private def extractChannelElm(tpe: Type): Type = {
    // Helper: extract T from a single channel type (Sender[T], Receiver[T], or Mpmc[T, rc]).
    def elmFromChan(chan: Type): Option[Type] = chan match {
      case Type.Apply(Type.Apply(_, elm, _), _, _) => Some(elm)  // Mpmc[T, rc] → T
      case Type.Apply(_, elm, _)                   => Some(elm)  // Sender[T] → T
      case _                                       => None
    }
    tpe match {
      // Tuple: (ChanType1, ChanType2) — extract from first element
      case Type.Apply(Type.Apply(_, firstChan, _), _, _) => elmFromChan(firstChan).getOrElse(tpe)
      case _ => tpe
    }
  }

  /**
    * Rewrites `Sender[t]`/`Receiver[t]` to `Concurrent.Channel.Mpmc[t, IO]`, recursively —
    * mirrors `SolutionLowering.lowerType`'s Sender/Receiver case. Used ONLY for flows targeting
    * the `@LoweringTargetChannel` defs, whose lookup keys are built from lowered types; it must
    * NOT be applied in `typeToMonoArg` generally, or ordinary defs' keys (e.g. `Channel.send`,
    * which keep `Sender`/`Receiver`) would be corrupted.
    */
  private[monomorph2] def lowerChannelType(tpe: Type): Type = tpe match {
    case Type.Apply(Type.Cst(TypeConstructor.Sender, loc), elm, _) =>
      Type.Apply(Type.Apply(Symbols.Types.ChannelMpmc, lowerChannelType(elm), loc), Type.IO, loc)
    case Type.Apply(Type.Cst(TypeConstructor.Receiver, loc), elm, _) =>
      Type.Apply(Type.Apply(Symbols.Types.ChannelMpmc, lowerChannelType(elm), loc), Type.IO, loc)
    case Type.Apply(t1, t2, loc) =>
      Type.Apply(lowerChannelType(t1), lowerChannelType(t2), loc)
    case Type.Alias(sym, args, inner, loc) =>
      Type.Alias(sym, args.map(lowerChannelType), lowerChannelType(inner), loc)
    case other => other
  }

  /** Converts `tpe0` to a `MonoArg` relative to the current declaration context. */
  private def typeToMonoArg(tpe0: Type)(implicit ctx: Context): MonoArg = {
    val tpe = Type.eraseAliases(tpe0)
    tpe match {
      case Type.Var(sym, _) =>
        ctx.tparamEnv.get(sym) match {
          case Some(idx) => MonoArg.Param(ctx.currentDecl, idx)
          case None =>
            // A type variable that is not a tparam of the current decl — e.g. a region var
            // introduced by `region r { ... }`, which is local to the expression. Mirroring
            // Specialization.default, such vars do not drive specialization: record them as an
            // opaque constant so the flow is still emitted but the solver does not propagate them.
            MonoArg.Const(tpe)
        }
      case at @ Type.AssocType(symUse, arg, kind, assocLoc) =>
        // Ground: resolve eagerly. Non-ground: record symbolically for the solver.
        if (tpe.typeVars.isEmpty) MonoArg.Const(MonomorphCanon.reduceAssocType(at)(ctx.root, ctx.flix))
        else MonoArg.Assoc(symUse.sym, typeToMonoArg(arg), kind, assocLoc)
      case Type.Cst(_, _) | _: Type.BaseType =>
        MonoArg.Const(tpe)
      case Type.Apply(_, _, _) =>
        if (tpe.kind == Kind.Eff && tpe.typeVars.isEmpty)
          // simplify reduces any AssocType nested in the formula (e.g. `Foo.Aef[a] + IO`) before
          // folding it via canonicalEffect — calling canonicalEffect directly would throw, since
          // evalEffect has no AssocType case.
          MonoArg.Const(MonomorphCanon.simplify(tpe, isGround = true)(ctx.root, ctx.flix))
        else {
          val (head, args) = MonomorphHelpers.flattenApply(tpe)
          MonoArg.App(typeToMonoArg(head), args.map(arg => typeToMonoArg(arg)))
        }
      case other =>
        MonoArg.Const(other)
    }
  }

  /** Returns the enum/struct `MonoVar` and type arguments of `tpe0`. */
  private def getEnumMonoVarAndTypeArgs(tpe0: Type, loc: SourceLocation): (MonoVar, List[Type]) = {
    val tpe = Type.eraseAliases(tpe0)
    val (head, args) = MonomorphHelpers.flattenApply(tpe)
    head match {
      case Type.Cst(TypeConstructor.Enum(sym, _), _)             => (MonoVar.Enum(sym), args)
      case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) => (MonoVar.RestrictableEnum(sym), args)
      case Type.Cst(TypeConstructor.Struct(sym, _), _)           => (MonoVar.Struct(sym), args)
      case _ => throw InternalCompilerException(s"Expected an Enum, RestrictableEnum, or Struct type, but got $tpe", loc)
    }
  }

}
