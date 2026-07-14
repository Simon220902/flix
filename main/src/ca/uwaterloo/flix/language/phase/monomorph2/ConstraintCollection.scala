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

import scala.annotation.tailrec


/**
  * Constraint generation for constraint-based monomorphization.
  *
  * Walks the treeshaken `TypedAst` root and, for every definition, enum, trait instance, and
  * default trait implementation, emits `Flow` constraints describing how concrete types and type
  * shapes propagate into the type-parameter slots of the definitions and enums it references.
  * `ConstraintSolver` later solves these constraints to find every concrete instantiation each
  * definition/enum needs to be specialized at.
  */
object ConstraintCollection {

  /**
    * A specialization target (definition or enum).
    */
  sealed trait MVar

  object MVar {
    case class Def(sym: Symbol.DefnSym) extends MVar

    case class Enum(sym: Symbol.EnumSym) extends MVar

    case class Sig(sym: Symbol.SigSym) extends MVar

    case class RestrictableEnum(sym: Symbol.RestrictableEnumSym) extends MVar

    case class Struct(sym: Symbol.StructSym) extends MVar
  }

  /**
    * A symbolic monomorphization argument or type component.
    */
  sealed trait MonoArg

  object MonoArg {
    /**
      * The i'th type parameter slot belonging to a specific MVar.
      * Tracks exactly: "The index'th type parameter of function/enum v"
      */
    case class Param(v: MVar, index: Int) extends MonoArg

    /**
      * A concrete / monomorphic type constant.
      */
    case class Const(tpe: Type) extends MonoArg

    /**
      * A type constructor applied to symbolic mono-arguments.
      * `tycon` is itself a MonoArg so higher-kinded type params can appear as the head.
      */
    case class App(tycon: MonoArg, args: List[MonoArg]) extends MonoArg

    /**
      * An associated type applied to a symbolic mono-argument.
      * E.g. `Collection.Elm[a]` in a polymorphic context becomes `Assoc(Elm, Param(v, i))`.
      * Resolved to a concrete type by the solver via the EqualityEnv.
      * `kind` and `loc` are stored so the solver can reconstruct `Type.AssocType` for reduction.
      */
    case class Assoc(sym: Symbol.AssocTypeSym, arg: MonoArg, kind: Kind, loc: SourceLocation) extends MonoArg
  }

  /** Returns every `(MVar, index)` pair referenced by a `Param` inside `arg`, however deeply wrapped. */
  def collectParams(arg: MonoArg): List[(MVar, Int)] = arg match {
    case MonoArg.Const(_)          => Nil
    case MonoArg.Param(v, i)       => List((v, i))
    case MonoArg.App(tycon, args)  => collectParams(tycon) ++ args.flatMap(collectParams)
    case MonoArg.Assoc(_, a, _, _) => collectParams(a)
  }

  sealed trait FlowInput
  object FlowInput {
    case class FlowArgs(args: List[MonoArg]) extends FlowInput
  }

  /**
    * A component-wise flow constraint.
    * Read as: "The type shape or constant `src` flows into the parameter slot `dst`"
    */
  case class Flow(src: FlowInput, dst: MVar)

  /**
    * Generation context.
    *
    * @param currentDecl the decl which we are currently traversing
    * @param tparamEnv maps the current def's type parameters to their indices
    * @param root the typed AST root (needed to resolve ground associated types)
    * @param flix the Flix context (needed by TypeReduction2)
    */
  case class Context(
    currentDecl: MVar,
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
        implicit val ctx: Context = Context(MVar.Def(defn.sym), tparamEnv, root, flix)
        visitDef(defn, Nil)
      }
    }.flatten.toSet

    val fromEnums = ParOps.parMap(root.enums.values) { enm =>
      val tparamEnv = enm.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.Enum(enm.sym), tparamEnv, root, flix)
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
          implicit val ctx: Context = Context(MVar.Def(instDef.sym), instTparamEnv ++ specTparamEnv, root, flix)
          visitDef(instDef, Nil)
        }
      }
    }.flatten.toSet

    val fromRestrictableEnums = ParOps.parMap(root.restrictableEnums.values) { enm =>
      val tparamEnv = (enm.index :: enm.tparams).zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.RestrictableEnum(enm.sym), tparamEnv, root, flix)
      visitRestrictableEnum(enm, Nil)
    }.flatten.toSet

    val fromStructs = ParOps.parMap(root.structs.values) { struct =>
      val tparamEnv = struct.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.Struct(struct.sym), tparamEnv, root, flix)
      visitStruct(struct, Nil)
    }.flatten.toSet

    // Visit default trait implementations (root.sigs with exp.isDefined).
    // These bodies contain calls to regular defs and need their flows tracked so the solver
    // can propagate when the sig is dispatched to its default impl.
    val fromSigs = ParOps.parMap(root.sigs.values.filter(_.exp.isDefined)) { sig =>
      // The trait's own tparam (e.g. `t` in `Foldable[t]`) is NOT in sig.spec.tparams but IS
      // a free variable in the default impl body. Include it at index 0 so typeToMonoArg can
      // represent it as Param(defnSym, 0). Solver tuple layout: [traitType, ...sig-own args].
      val trt = root.traits(sig.sym.trt)
      val traitTparam = trt.tparam
      val allTparams = traitTparam :: sig.spec.tparams
      val tparamEnv = allTparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      val ns = sig.sym.trt.namespace :+ sig.sym.trt.name
      val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
      flix.profile(defnSym, sig.sym.loc) {
        implicit val ctx: Context = Context(MVar.Def(defnSym), tparamEnv, root, flix)
        sig.exp.map(e => visitExp(e, Nil)).getOrElse(Nil)
      }
    }.flatten.toSet

    fromDefs ++ fromEnums ++ fromInstances ++ fromRestrictableEnums ++ fromStructs ++ fromSigs
  }(MonomorphDebug.DebugFlows)

  // ---- Constraint generation ---------------------------------------------
  //
  // Every visit* function below threads an explicit, immutable `acc: List[Flow]` accumulator
  // through the walk instead of returning `Set[Flow]` and unioning results with `++` on the way
  // back up. Each node conses its own flow(s) onto the accumulator it receives and passes the
  // result to its next sibling — a plain `foldLeft`/cons shape, no mutation, no per-node Set
  // allocation or hashing. Flows may genuinely duplicate (e.g. the same call site's flow
  // re-derived from two visits); that's fine, since dedup only needs to happen once, in
  // `generate`'s final `.toSet` per category, rather than paying an O(n) merge cost at every node.

  /**
    * Emits flow constraints for enum type applications occurring in `tpe`.
    */
  private def visitType(tpe0: Type, acc: List[Flow])(implicit ctx: Context): List[Flow] = dealias(tpe0) match {
    case at @ Type.AssocType(_, arg, _, _) =>
      // If the associated type is ground, resolve it and continue; otherwise recurse into arg.
      if (tpe0.typeVars.isEmpty) visitType(MonomorphCanon.reduceAssocType(at)(ctx.root, ctx.flix), acc)
      else visitType(arg, acc)
    case _: Type.BaseType
         | Type.Var(_, _)
         | Type.Cst(_, _) => acc
    case app @ Type.Apply(_, _, loc) =>
      val (appHead, tpArgs) = flattenApply(app)
      val acc1 = tpArgs.foldLeft(acc)((a, t) => visitType(t, a))
      val mvarOpt = appHead match {
        case Type.Cst(TypeConstructor.Enum(sym, _), _)             => Some(MVar.Enum(sym))
        case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) => Some(MVar.RestrictableEnum(sym))
        case Type.Cst(TypeConstructor.Struct(sym, _), _)           => Some(MVar.Struct(sym))
        case _                                                     => None
      }
      mvarOpt match {
        case Some(mvar) => Flow(FlowInput.FlowArgs(tpArgs.map(t => typeToMonoArg(t))), mvar) :: acc1
        case None       => acc1
      }
  }

  /**
    * Emits flow constraints for all case field types in `enumDecl`.
    */
  private def visitEnum(enumDecl: TypedAst.Enum, acc: List[Flow])(implicit ctx: Context): List[Flow] =
    enumDecl.cases.values.foldLeft(acc) { (a, cas) => cas.tpes.foldLeft(a)((a2, t) => visitType(t, a2)) }

  /**
    * Emits flow constraints for all case field types in `enumDecl`.
    */
  private def visitRestrictableEnum(enumDecl: TypedAst.RestrictableEnum, acc: List[Flow])(implicit ctx: Context): List[Flow] =
    enumDecl.cases.values.foldLeft(acc) { (a, cas) => cas.tpes.foldLeft(a)((a2, t) => visitType(t, a2)) }

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
    // LOWERING
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
          FlowInput.FlowArgs(List(typeToMonoArg(eff), typeToMonoArg(defn.spec.retTpe))),
          MVar.Def(handler.handlerSym)
        )
        // Canonicalized to match SolutionLowering.wrapInHandler, which threads the canonical (not
        // raw formula) effect into the next handler wrap via this same MonomorphCanon.canonicalEffect call.
        eff = MonomorphCanon.canonicalEffect(Type.mkUnion(Type.mkDifference(eff, handler.handledEff, loc), Type.IO, loc))
        flow :: a
      }
    }
  }

  /**
    * Emits flow constraints for all call sites and enum usages in `exp`.
    *
    * Scope: all TypedAst expression forms are covered. Datalog fixpoint nodes emit the
    * Box/Unbox/liftN/lattice/Facts/ProjectInto/ProvenanceOf constraints for whatever
    * `SolutionLowering.scala` will synthesize for them (see the `// LOWERING`-marked cases below).
    * Channel nodes (NewChannel, GetChannel, etc.) likewise emit constraints for their synthesized
    * stdlib calls directly, rather than relying on a pre-lowering pass.
    */
  private def visitExp(exp: Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = exp match {
    case Expr.Cst(_, _, _) => acc
    case Expr.Var(_, _, _) => acc
    case Expr.Hole(_, _, _, _, _) => acc

    case Expr.ApplyDef(symUse, exps, targs, _, _, _, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(FlowInput.FlowArgs(targs.map(typeToMonoArg(_))), MVar.Def(symUse.sym)) :: acc1

    case Expr.ApplySig(symUse, exps, targ, targs, _, _, _, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(FlowInput.FlowArgs((targ :: targs).map(typeToMonoArg(_))), MVar.Sig(symUse.sym)) :: acc1

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
        case (a, MatchRule(_, guardOpt, body, _)) =>
          val a1 = guardOpt.foldLeft(a)((a2, g) => visitExp(g, a2))
          visitExp(body, a1)
      }

    // PRE-LOWERING: pre-lowering will rewrite RestrictableTag to Tag over MVar.Enum; until then,
    // both are handled identically here (getEnumMVarAndTypeArgs dispatches on `tpe` itself, not
    // on which Expr node matched) — the solver just needs to handle both resulting mvars.
    case Expr.Tag(_, exps, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMVarAndTypeArgs(tpe, loc)
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(FlowInput.FlowArgs(tpArgs.map(typeToMonoArg(_))), mvar) :: acc1

    // LOWERING
    case Expr.RestrictableTag(_, exps, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMVarAndTypeArgs(tpe, loc)
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      Flow(FlowInput.FlowArgs(tpArgs.map(typeToMonoArg(_))), mvar) :: acc1

    // LOWERING
    case Expr.RestrictableChoose(_, exp, rules, _, _, _) =>
      // PRE-LOWERING: pre-lowering will rewrite RestrictableChoose to Match.
      // Until then we recurse structurally — correct since no new call sites are introduced.
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

    // StructNew: mirrors Expr.Tag — emits a Flow for the struct's own MVar so a construction
    // site's concrete type args seed the solver (visitType alone only captures the DECLARATION's
    // own field-type structure, not where/at-what-types the struct is actually instantiated).
    case Expr.StructNew(_, fields, region, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMVarAndTypeArgs(tpe, loc)
      val acc1 = fields.foldLeft(acc) { case (a, (_, e)) => visitExp(e, a) }
      val acc2 = region.foldLeft(acc1)((a, r) => visitExp(r, a))
      Flow(FlowInput.FlowArgs(tpArgs.map(typeToMonoArg(_))), mvar) :: acc2

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

    // LOWERING
    // ParYield: Lowering synthesizes Channel.get, Channel.put, Channel.newChannel calls
    // for each non-last fragment. Emit flows so the solver pre-populates these.
    case Expr.ParYield(frags, exp, _, _, loc) =>
      val acc1 = frags.foldLeft(acc)((a, f) => visitExp(f.exp, a))
      val acc2 = visitExp(exp, acc1)
      frags.init.foldLeft(acc2) { (a, frag) =>
        val elmType = frag.exp.tpe
        val elmArg = typeToMonoArg(lowerChannelType(elmType))
        Flow(FlowInput.FlowArgs(List(elmArg)), MVar.Def(Defs.ChannelNew)) ::
          Flow(FlowInput.FlowArgs(List(elmArg)), MVar.Def(Defs.ChannelPut)) ::
          Flow(FlowInput.FlowArgs(List(elmArg)), MVar.Def(Defs.ChannelGet)) :: a
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

    // LOWERING
    // Channel nodes: recurse into sub-expressions AND emit flows for the @LoweringTargetChannel
    // defs that Lowering will synthesize at code-gen time.
    // GetChannel(<- c) → Channel.get(c): tparam a = element type = tpe
    case Expr.GetChannel(exp, tpe, _, loc) =>
      val acc1 = visitExp(exp, acc)
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(lowerChannelType(tpe)))), MVar.Def(Defs.ChannelGet)) :: acc1

    // LOWERING
    // PutChannel(channel, value) → Channel.put(value, channel): tparam a = exp2.tpe (value type)
    case Expr.PutChannel(exp1, exp2, _, _, loc) =>
      val acc1 = visitExp(exp2, visitExp(exp1, acc))
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(lowerChannelType(exp2.tpe)))), MVar.Def(Defs.ChannelPut)) :: acc1

    // LOWERING
    // NewChannel → Channel.newChannelTuple(size): tparam a = element type from Mpmc[a, rc]
    // tpe may be (Mpmc[T, rc], Mpmc[T, rc]) (tuple) or Mpmc[T, rc] (single channel).
    case Expr.NewChannel(exp, tpe, _, loc) =>
      val elmType = extractChannelElm(tpe)
      val acc1 = visitExp(exp, acc)
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(lowerChannelType(elmType)))), MVar.Def(Defs.ChannelNewTuple)) :: acc1

    // LOWERING
    // SelectChannel: Lowering synthesizes, per rule, a Channel.mpmcAdmin call (to build the
    // admin list passed to the non-parametric Channel.selectFrom) and a Channel.unsafeGetAndUnlock
    // call (to read the winning channel's value) — NOT Channel.get, which is only for the
    // simple blocking `<- ch` form (Expr.GetChannel). The admin values are collected into a
    // `List[ChannelMpmcAdmin]` built directly via `mkTag`/`mkList` (SolutionLowering.mkAdmins),
    // same bypass-the-ordinary-rewrite-path situation as latticeFlows/FixpointLambda above — the
    // `List[ChannelMpmcAdmin]` instantiation is fixed (not per-rule/per-elmType) and must be
    // predicted here too.
    case Expr.SelectChannel(rules, default, _, _, loc) =>
      val acc1 = rules.foldLeft(acc) { (a, r) =>
        val elmType = r.chan.tpe match {
          case Type.Apply(Type.Apply(_, e, _), _, _) => e  // Mpmc[T, rc] → T
          case Type.Apply(_, e, _)                    => e  // Sender[T] / Receiver[T] → T
          case t                                      => t
        }
        val elmArg = typeToMonoArg(lowerChannelType(elmType))
        val a1 = visitExp(r.exp, visitExp(r.chan, a))
        Flow(FlowInput.FlowArgs(List(elmArg)), MVar.Def(Defs.ChannelUnsafeGetAndUnlock)) ::
          Flow(FlowInput.FlowArgs(List(elmArg)), MVar.Def(Defs.ChannelMpmcAdmin)) :: a1
      }
      val acc2 = default.foldLeft(acc1)((a, d) => visitExp(d, a))
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(Types.ChannelMpmcAdmin))), MVar.Enum(Enums.FList)) :: acc2

    // LOWERING
    // Datalog fixpoint nodes: in addition to
    // recursing into sub-expressions to capture any defs called inside predicates, emit flows
    // for every Box/Unbox/liftN/lattice/Facts/ProjectInto/ProvenanceOf call that
    // SolutionLowering.scala will synthesize for these constructs — mirroring exactly the
    // TypedAst structure lowering itself inspects.
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

    // LOWERING
    // FixpointLambda: Lowering builds a `List[PredSym]` value directly via `mkTag`/`mkList`
    // (SolutionLowering.mkList, called from its FixpointLambda case) to pass to Solver.rename —
    // same bypass-the-ordinary-rewrite-path situation as latticeFlows' Denotation.Relational case
    // above, so the `List[PredSym]` instantiation must be predicted here too.
    case Expr.FixpointLambda(_, exp, _, _, loc) =>
      val acc1 = visitExp(exp, acc)
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(Types.PredSym))), MVar.Enum(Enums.FList)) :: acc1

    case Expr.FixpointMerge(exp1, exp2, _, _, _) =>
      visitExp(exp2, visitExp(exp1, acc))

    case Expr.FixpointSolveWithProject(exps, _, _, _, _, _) =>
      exps.foldLeft(acc)((a, e) => visitExp(e, a))

    // LOWERING
    // InjectInto: Lowering synthesizes a call to Fixpoint3.Solver.injectIntoN(p, ts), generic
    // over the container type constructor `f` and the tuple's own component types `t1..tn`.
    case Expr.FixpointInjectInto(exps, _, _, _, loc) =>
      exps.foldLeft(acc) { (a, e) =>
        val (tycon, argTypes) = dealias(e.tpe) match {
          case Type.Apply(tc, innerType0, _) =>
            val innerType = dealias(innerType0)
            innerType.typeConstructor match {
              case Some(TypeConstructor.Tuple(_)) => (tc, innerType.typeArguments)
              case Some(TypeConstructor.Unit)     => (tc, Nil)
              case _                              => (tc, List(innerType))
            }
          case t => throw InternalCompilerException(s"Unexpected non-foldable type: '$t'.", loc)
        }
        val flowArgs = (tycon :: argTypes).map(typeToMonoArg(_))
        val a1 = visitExp(e, a)
        Flow(FlowInput.FlowArgs(flowArgs), MVar.Def(Defs.ProjectInto(argTypes.length))) :: a1
      }

    // LOWERING
    // Query-with-select: Lowering synthesizes a call to Fixpoint3.Solver.factsN(p, d), generic
    // over the N selected terms' own types. (The query's embedded constraint set, reached via
    // `queryExp`'s recursion into FixpointConstraintSet, already supplies the Box/liftN flows
    // for the underlying rule itself — `selects`/`from`/`where` here are the same information,
    // recursed into structurally only, as before.)
    case Expr.FixpointQueryWithSelect(exps, queryExp, selects, from, where, _, tpe0, _, loc) =>
      // Facts(arity)'s flow args come from the query's own resolved result type `tpe0`
      // (Vector[(t1,...,tn)], or Vector[t1] for arity 1 — matching Facts's declared signature),
      // NOT from `selects`' own term types: those are typed in the query's local/row-polymorphic
      // scope and may still carry a locally-scoped type var never unified back into this def's
      // own substitution (unlike an ordinary lexically-bound expression).
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
      Flow(FlowInput.FlowArgs(argTypes.map(typeToMonoArg(_))), MVar.Def(Defs.Facts(arity))) :: acc5

    // LOWERING
    // Query-with-provenance: Lowering boxes every goal term, unboxes every term type of every
    // predicate the extensible-variant result type can carry, and calls Solver.provenanceOf and
    // (internally) Vector.get at a fixed Boxed type. See mkExtVarLambda/mkUnboxedTerm.
    case Expr.FixpointQueryWithProvenance(exps, select, _, tpe0, _, loc) =>
      val acc1 = exps.foldLeft(acc)((a, e) => visitExp(e, a))
      val acc2 = select match {
        case Predicate.Head.Atom(_, _, terms, _, _) =>
          val s1 = terms.foldLeft(acc1)((a, t) => visitExp(t, a))
          terms.foldLeft(s1)((a, t) => boxFlow(t.tpe) :: a)
      }
      val extVarType = unwrapVectorType(tpe0, loc)
      val acc3 = predicatesOfExtVar(extVarType, loc).flatMap(_._2).foldLeft(acc2) { (a, t) =>
        Flow(FlowInput.FlowArgs(List(typeToMonoArg(t))), MVar.Def(Defs.Unbox)) :: a
      }
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(Types.Boxed))), MVar.Def(Defs.VectorGet)) ::
        Flow(FlowInput.FlowArgs(List(typeToMonoArg(extVarType))), MVar.Def(Defs.ProvenanceOf)) :: acc3

    case Expr.Error(_, _, _) => acc
  }

  // ---- Datalog helpers --------------------------------------
  //
  // Each of these mirrors, structurally, the corresponding synthesis logic in
  // SolutionLowering.scala (named in each doc comment).

  /**
    * Strips `Type.Alias` wrappers before structural matching. Needed anywhere this file
    * pattern-matches a raw `Type` directly (`typeToMonoArg` already dealiases on its own path) —
    * unlike `SolutionLowering.scala`, which runs on an already-specialized MonoAst tree (aliases
    * stripped earlier by `StrictSubstitution`), this file walks the raw, ground `TypedAst`, where
    * a user type alias (e.g. `type alias X = List[Int32]`) is still intact. Also used by
    * `visitType`/`getEnumMVarAndTypeArgs`: `Type.Alias` extends `Type.BaseType`, so without this,
    * an enum/struct field declared via an alias name (e.g. `case Foo(BoxedDenotation)`) silently
    * matches `visitType`'s `BaseType` catch-all instead of the `Type.Apply` case that emits its
    * flow — no crash, just a silently missing flow for that instantiation.
    */
  private def dealias(tpe: Type): Type = tpe match {
    case Type.Alias(_, _, inner, _) => dealias(inner)
    case t => t
  }

  private def isQuantifiedVar(sym: Symbol.VarSym, cparams0: List[TypedAst.ConstraintParam]): Boolean =
    cparams0.exists(p => p.bnd.sym == sym)

  private def quantifiedVars(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr): List[(Symbol.VarSym, Type)] =
    TypedAstOps.freeVars(exp0).toList.filter { case (sym, _) => isQuantifiedVar(sym, cparams0) }

  /** A flow for `Fixpoint3.Boxable.box` at type `tpe` — mirrors `SolutionLowering.box`. */
  private def boxFlow(tpe: Type)(implicit ctx: Context): Flow =
    Flow(FlowInput.FlowArgs(List(typeToMonoArg(tpe))), MVar.Def(Defs.Box))

  /**
    * Flows for a head term — mirrors `SolutionLowering.lowerHeadTerm`'s cases 1.2/2/3: a
    * lexically-bound Var, or a non-Var term with no quantified free vars, is boxed; a non-Var
    * term WITH quantified free vars is lifted via `lift{arity}` instead (never both). A
    * quantified Var itself (case 1.1) needs neither flow — it carries no runtime value of its own.
    */
  private def headTermFlows(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = exp0 match {
    case Expr.Var(sym, tpe, _) =>
      if (isQuantifiedVar(sym, cparams0)) acc else boxFlow(tpe) :: acc
    case _ =>
      val fvs = quantifiedVars(cparams0, exp0)
      if (fvs.isEmpty) boxFlow(exp0.tpe) :: acc
      else Flow(FlowInput.FlowArgs((fvs.map(_._2) :+ exp0.tpe).map(typeToMonoArg(_))), MVar.Def(Defs.Lift(fvs.length))) :: acc
  }

  /**
    * Flows for a body atom's terms — mirrors `SolutionLowering.lowerBodyTerm`: `Wild` and a
    * quantified `Var` need nothing; a non-quantified `Var` or any `Cst` is boxed.
    */
  private def bodyAtomTermFlows(cparams0: List[TypedAst.ConstraintParam], terms: List[TypedAst.Pattern], acc: List[Flow])(implicit ctx: Context): List[Flow] =
    terms.foldLeft(acc) {
      case (a, TypedAst.Pattern.Wild(_, _)) => a
      case (a, TypedAst.Pattern.Var(bnd, tpe, _)) =>
        if (isQuantifiedVar(bnd.sym, cparams0)) a else boxFlow(tpe) :: a
      case (a, TypedAst.Pattern.Cst(_, tpe, _)) => boxFlow(tpe) :: a
      case (a, _) => a
    }

  /**
    * A flow for `lift{arity}b`, mirroring `SolutionLowering.mkGuard`. An arity-0 guard is
    * lowered to a plain closure with no lift call at all (`Guard0` — there is no `lift0b`), so
    * nothing is emitted in that case.
    */
  private def guardLiftFlow(cparams0: List[TypedAst.ConstraintParam], exp0: TypedAst.Expr, acc: List[Flow])(implicit ctx: Context): List[Flow] = {
    val fvs = quantifiedVars(cparams0, exp0)
    if (fvs.isEmpty) acc
    else Flow(FlowInput.FlowArgs(fvs.map(kv => typeToMonoArg(kv._2))), MVar.Def(Defs.LiftB(fvs.length))) :: acc
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
    val inVars = quantifiedVars(cparams0, exp0)
    val inner = dealias(exp0.tpe) match {
      case Type.Apply(Type.Cst(TypeConstructor.Vector, _), t, _) => dealias(t)
      case t => throw InternalCompilerException(s"Expected Vector[_], but got $t", loc)
    }
    val outTypes = if (outArity <= 1) List(inner) else inner.typeArguments
    Flow(FlowInput.FlowArgs((inVars.map(_._2) ++ outTypes).map(typeToMonoArg(_))), MVar.Def(Defs.LiftXM(inVars.length, outArity)))
  }

  /**
    * Flows for `Fixpoint3.Ast.Shared.lattice`/`box`/`Denotation`, mirroring
    * `SolutionLowering.mkDenotation`. The `Relational` case constructs a `Denotation[Boxed]` value
    * directly via `mkTag`, bypassing the ordinary TypedAst-level rewrite path entirely, so its
    * enum-construction flow must be predicted here the same way channels/Box/Unbox/liftN already
    * are, or `enumTable` never gets an entry for it and `SolutionSpecialization`'s post-lowering
    * rewrite pass silently falls back to the original, unspecialized `Denotation` declaration.
    */
  private def latticeFlows(den: Denotation, lastTermType: Option[Type], loc: SourceLocation, acc: List[Flow])(implicit ctx: Context): List[Flow] = den match {
    case Denotation.Relational =>
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(Types.Boxed))), MVar.Enum(Enums.Denotation)) :: acc
    case Denotation.Latticenal =>
      val tpe = lastTermType.getOrElse(throw InternalCompilerException("Unexpected nullary lattice predicate.", loc))
      Flow(FlowInput.FlowArgs(List(typeToMonoArg(tpe))), MVar.Def(Defs.Lattice)) ::
        Flow(FlowInput.FlowArgs(List(typeToMonoArg(tpe))), MVar.Def(Defs.LatticeBox)) :: acc
  }

  /** Returns `t` from `Vector[t]` — mirrors `SolutionLowering.unwrapVectorType`. */
  private def unwrapVectorType(tpe: Type, loc: SourceLocation): Type = dealias(tpe) match {
    case Type.Apply(Type.Cst(TypeConstructor.Vector, _), extType, _) => dealias(extType)
    case t => throw InternalCompilerException(s"Expected Type.Apply(Type.Cst(TypeConstructor.Vector, _), _, _), but got $t", loc)
  }

  /** Mirrors `SolutionLowering.predicatesOfExtVar`. */
  private def predicatesOfExtVar(tpe: Type, loc: SourceLocation): List[(Name.Pred, List[Type])] = dealias(tpe) match {
    case Type.Apply(Type.Cst(TypeConstructor.Extensible, _), tpe1, loc1) => predicatesOfSchemaRow(dealias(tpe1), loc1)
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
    * Mirrors `SolutionLowering.termTypesOfRelation`, with one addition: `SolutionLowering` runs
    * post-solve, where a stray `Kind.Star` var reaching this point has already been defaulted to
    * `AnyType` (its own `AnyType` case, kept below); this file runs pre-solve, on raw `TypedAst`,
    * where a relation belonging to an unused/under-constrained provenance predicate can still be
    * a genuinely-unresolved bare `Type.Var` at this point. Correctness requirement: such a var
    * must NOT be defaulted through to an Unbox flow (that defaulting is unsound specifically for
    * Box/Unbox/liftN) — so it is simply skipped here
    * (no term types recoverable for this relation) rather than defaulted or thrown: a genuine miss
    * still surfaces as a clean Solver gap downstream, exactly as it would if no flow existed here.
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
    * mirrors `SolutionLowering.lowerType`'s Sender/Receiver case.
    *
    * Used ONLY when building flows for the `@LoweringTargetChannel` defs (`Defs.ChannelGet` /
    * `ChannelPut` / `ChannelNewTuple`), because `SolutionLowering.mkGetChannel` / `mkPutChannel` /
    * `mkNewChannel` query `lookup` with a type that has already been run through
    * `SolutionLowering.lowerType`. It must NOT be applied inside `typeToMonoArg` generally: an
    * ordinary def's own specialization key (e.g. `Channel.send`) is built from `subst(itpe)`,
    * which never calls `lowerType` and so keeps `Sender`/`Receiver` unexpanded — rewriting those
    * flows too would corrupt that def's own defTable key instead of fixing the channel-def one.
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

  /** Walks `tpe`'s `Type.Apply` chain once, returning its head and its args in left-to-right order. */
  private def flattenApply(tpe: Type): (Type, List[Type]) = {
    @tailrec
    def loop(t: Type, argsAcc: List[Type]): (Type, List[Type]) = t match {
      case Type.Apply(t1, t2, _) => loop(t1, t2 :: argsAcc)
      case head => (head, argsAcc)
    }
    loop(tpe, Nil)
  }

  /**
    * Converts `tpe` to a `MonoArg` relative to the current declaration context.
    * Type variables bound by the current declaration become `Param`; everything else becomes `Const` or `App`.
    */
  private def typeToMonoArg(tpe: Type)(implicit ctx: Context): MonoArg = tpe match {
    case Type.Var(sym, _) =>
      ctx.tparamEnv.get(sym) match {
        case Some(idx) => MonoArg.Param(ctx.currentDecl, idx)
        case None =>
          // DESIGN NOTE — locally-scoped type variables (e.g. region vars):
          //
          // Unlike Specialization.scala (which is demand-driven and always has a fully-ground
          // substitution when it descends into a def body), we process every def statically
          // with only its *declared* type parameters in scope. This means we can encounter
          // type variables that are NOT type parameters of the current def — specifically,
          // region variables introduced by `region r { ... }` expressions, which are fresh
          // variables local to that expression and do not appear in `spec.tparams`.
          //
          // Example: `def f(): Unit = region r { Array.empty(r, 0); () }`
          // When visiting the `ApplyDef(Array.empty, targs=[r, Int32])` inside the region,
          // `r` is a Type.Var with no entry in tparamEnv.
          //
          // The correct treatment here mirrors Specialization.defaultType: region vars do not
          // drive specialization, so we record them as an opaque constant. The resulting Flow
          // is still emitted (preserving reachability), but the region arg is fixed and the
          // solver will not propagate it further. If this causes incorrect constraints in the
          // future, look here first — the fix might require tracking region vars separately
          // or filtering them out of the flow args.
          MonoArg.Const(tpe)
      }
    case at @ Type.AssocType(symUse, arg, kind, assocLoc) =>
      // Ground: resolve eagerly. Non-ground: record symbolically for the solver.
      if (tpe.typeVars.isEmpty) MonoArg.Const(MonomorphCanon.reduceAssocType(at)(ctx.root, ctx.flix))
      else MonoArg.Assoc(symUse.sym, typeToMonoArg(arg), kind, assocLoc)
    case Type.Alias(_, _, inner, _) =>
      typeToMonoArg(inner)
    case Type.Cst(_, _) | _: Type.BaseType =>
      MonoArg.Const(tpe)
    case Type.Apply(_, _, _) =>
      if (tpe.kind == Kind.Eff && tpe.typeVars.isEmpty)
        // Guard: effect formulas occasionally contain non-effect constructors (e.g. data types in
        // complement/union positions). canonicalEffect will throw on those; fall back to Const.
        try MonoArg.Const(MonomorphCanon.canonicalEffect(tpe))
        catch { case _: ca.uwaterloo.flix.util.InternalCompilerException => MonoArg.Const(tpe) }
      else {
        val (head, args) = flattenApply(tpe)
        MonoArg.App(typeToMonoArg(head), args.map(arg => typeToMonoArg(arg)))
      }
    case other =>
      MonoArg.Const(other)
  }

  /** Returns the enum/struct `MVar` and type arguments for a fully-applied enum/struct type. */
  private def getEnumMVarAndTypeArgs(tpe0: Type, loc: SourceLocation): (MVar, List[Type]) = {
    val tpe = dealias(tpe0)
    val (head, args) = flattenApply(tpe)
    head match {
      case Type.Cst(TypeConstructor.Enum(sym, _), _)             => (MVar.Enum(sym), args)
      case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) => (MVar.RestrictableEnum(sym), args)
      case Type.Cst(TypeConstructor.Struct(sym, _), _)           => (MVar.Struct(sym), args)
      case _ => throw InternalCompilerException(s"ConstraintGen: bad types? ${tpe}", loc)
    }
  }

}
