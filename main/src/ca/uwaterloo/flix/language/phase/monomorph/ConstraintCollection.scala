/*
 * Copyright 2025 Simon Lykke Andersen
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
import ca.uwaterloo.flix.language.ast.TypedAst.{Expr, FormalParam, MatchRule, Predicate}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.util.collection.CofiniteSet
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}
import ca.uwaterloo.flix.language.phase.typer.{Progress, TypeReduction2}


// TODO: Add general explanation comment.
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
      * A concrete / monomorphic type constant.
      */
    case class Const(tpe: Type) extends MonoArg

    /**
      * The i'th type parameter slot belonging to a specific MVar.
      * Tracks exactly: "The index'th type parameter of function/enum v"
      */
    case class Param(v: MVar, index: Int) extends MonoArg

    /**
      * A type constructor applied to symbolic mono-arguments.
      */
    case class App(tycon: Type, args: List[MonoArg]) extends MonoArg

    /**
      * An associated type applied to a symbolic mono-argument.
      * E.g. `Collection.Elm[a]` in a polymorphic context becomes `Assoc(Elm, Param(v, i))`.
      * Resolved to a concrete type by the solver via the EqualityEnv.
      */
    case class Assoc(sym: Symbol.AssocTypeSym, arg: MonoArg) extends MonoArg
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
  def generate(root: TypedAst.Root)(implicit flix: Flix): Set[Flow] = {
    val fromDefs = ParOps.parMap(root.defs.values) { defn =>
      val tparamEnv = defn.spec.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.Def(defn.sym), tparamEnv, root, flix)
      visitDef(defn)
    }.flatten.toSet

    val fromEnums = ParOps.parMap(root.enums.values) { enm =>
      val tparamEnv = enm.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.Enum(enm.sym), tparamEnv, root, flix)
      visitEnum(enm)
    }.flatten.toSet

    val fromInstances = ParOps.parMap(root.instances.values) { inst =>
      val tparamEnv = inst.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      inst.defs.flatMap { instDef =>
        implicit val ctx: Context = Context(MVar.Def(instDef.sym), tparamEnv, root, flix)
        visitDef(instDef)
      }.toSet
    }.flatten.toSet

    val fromRestrictableEnums = ParOps.parMap(root.restrictableEnums.values) { enm =>
      val tparamEnv = (enm.index :: enm.tparams).zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.RestrictableEnum(enm.sym), tparamEnv, root, flix)
      visitRestrictableEnum(enm)
    }.flatten.toSet

    val fromStructs = ParOps.parMap(root.structs.values) { struct =>
      val tparamEnv = struct.tparams.zipWithIndex.map { case (tp, i) => tp.sym -> i }.toMap
      implicit val ctx: Context = Context(MVar.Struct(struct.sym), tparamEnv, root, flix)
      visitStruct(struct)
    }.flatten.toSet

    fromDefs ++ fromEnums ++ fromInstances ++ fromRestrictableEnums ++ fromStructs
  }

  /**
    * Renders `flows` as a Graphviz DOT string.
    *
    * Nodes are MVars (boxes=defs, ellipses=enums, diamonds=sigs).
    * Seed edges run from a plaintext constant node to the destination MVar.
    * Propagation edges run from the source MVar to the destination MVar.
    */
  def toDot(flows: Set[Flow]): String = {
    val sb = new StringBuilder
    sb.append("digraph constraints {\n")
    sb.append("  rankdir=LR;\n")
    sb.append("  node [fontname=\"Courier\", fontsize=10];\n")
    sb.append("  edge [fontname=\"Courier\", fontsize=8];\n\n")

    // Collect all MVars appearing anywhere in the flow set.
    val allMVars: Set[MVar] = flows.flatMap { case Flow(FlowInput.FlowArgs(args), dst) =>
      Set(dst) ++ args.flatMap(collectMVars)
    }

    // Emit one node per MVar.
    allMVars.foreach { mvar =>
      val (shape, color) = mvar match {
        case _: MVar.Def              => ("box",     "lightblue")
        case _: MVar.Enum             => ("ellipse", "lightyellow")
        case _: MVar.Sig              => ("diamond", "lightgreen")
        case _: MVar.RestrictableEnum => ("ellipse", "lightsalmon")
        case _: MVar.Struct           => ("box",     "lightcyan")
      }
      sb.append(s"""  ${dotId(mvar)} [label="${dotEscape(mvarLabel(mvar))}", shape=$shape, style=filled, fillcolor=$color];\n""")
    }

    sb.append("\n")

    // Emit edges. Flows with only Const/App args get a plaintext "seed" node.
    var seedCount = 0
    flows.foreach { case Flow(FlowInput.FlowArgs(args), dst) =>
      val srcMVars = args.flatMap(collectMVars)
      if (srcMVars.isEmpty) {
        val label = args.map(monoArgLabel).mkString(", ")
        val sid = s"seed$seedCount"
        seedCount += 1
        sb.append(s"""  $sid [label="${dotEscape(label)}", shape=plaintext];\n""")
        sb.append(s"""  $sid -> ${dotId(dst)};\n""")
      } else {
        val label = args.map(monoArgLabel).mkString(", ")
        srcMVars.distinct.foreach { src =>
          sb.append(s"""  ${dotId(src)} -> ${dotId(dst)} [label="${dotEscape(label)}"];\n""")
        }
      }
    }

    sb.append("}\n")
    sb.toString
  }

  // ---- DOT helpers -------------------------------------------------------

  private def collectMVars(arg: MonoArg): List[MVar] = arg match {
    case MonoArg.Const(_)       => Nil
    case MonoArg.Param(v, _)    => List(v)
    case MonoArg.App(_, args)   => args.flatMap(collectMVars)
    case MonoArg.Assoc(_, arg)  => collectMVars(arg)
  }

  private def dotId(mvar: MVar): String = {
    val raw = mvar match {
      case MVar.Def(sym)              => s"def_${sanitize(sym.toString)}"
      case MVar.Enum(sym)             => s"enum_${sanitize(sym.toString)}"
      case MVar.Sig(sym)              => s"sig_${sanitize(sym.toString)}"
      case MVar.RestrictableEnum(sym) => s"renum_${sanitize(sym.toString)}"
      case MVar.Struct(sym)           => s"struct_${sanitize(sym.toString)}"
    }
    s""""$raw""""
  }

  private def mvarLabel(mvar: MVar): String = mvar match {
    case MVar.Def(sym)              => s"Def(${sym.name})"
    case MVar.Enum(sym)             => s"Enum(${sym.name})"
    case MVar.Sig(sym)              => s"Sig(${sym.name})"
    case MVar.RestrictableEnum(sym) => s"REnum(${sym.name})"
    case MVar.Struct(sym)           => s"Struct(${sym.text})"
  }

  private def monoArgLabel(arg: MonoArg): String = arg match {
    case MonoArg.Const(tpe)     => tpe.toString
    case MonoArg.Param(v, i)    => s"p(${mvarLabel(v)},$i)"
    case MonoArg.App(tc, args)  => s"App($tc,${args.map(monoArgLabel).mkString(",")})"
    case MonoArg.Assoc(sym, a)  => s"Assoc(${sym.name},${monoArgLabel(a)})"
  }

  /** Replaces DOT-unsafe characters with underscores in node IDs. */
  private def sanitize(s: String): String =
    s.replaceAll("[^A-Za-z0-9_]", "_")

  /** Escapes double-quotes and backslashes for DOT label strings. */
  private def dotEscape(s: String): String =
    s.replace("\\", "\\\\").replace("\"", "\\\"")

  // ---- Constraint generation ---------------------------------------------

  /**
    * Emits flow constraints for enum type applications occurring in `tpe`.
    */
  private def visitType(tpe: Type)(implicit ctx: Context): Set[Flow] = tpe match {
    case Type.AssocType(_, arg, _, _) =>
      // If the associated type is ground, resolve it and continue; otherwise recurse into arg.
      if (tpe.typeVars.isEmpty) visitType(reduceAssocType(tpe))
      else visitType(arg)
    case _: Type.BaseType
         | Type.Var(_, _)
         | Type.Cst(_, _) => Set.empty
    case Type.Apply(_, _, loc) =>
      val tpArgs = getAppArgs(tpe)
      val inner = tpArgs.flatMap(visitType(_)).toSet
      getAppHead(tpe) match {
        case Type.Cst(TypeConstructor.Enum(sym, _), _) =>
          val margs = tpArgs.map(typeToMonoArg(_, loc))
          inner + Flow(FlowInput.FlowArgs(margs), MVar.Enum(sym))
        case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) =>
          val margs = tpArgs.map(typeToMonoArg(_, loc))
          inner + Flow(FlowInput.FlowArgs(margs), MVar.RestrictableEnum(sym))
        case _ => inner
      }
  }

  /**
    * Emits flow constraints for all case field types in `enumDecl`.
    */
  private def visitEnum(enumDecl: TypedAst.Enum)(implicit ctx: Context): Set[Flow] =
    enumDecl.cases.values.flatMap(cas => cas.tpes.flatMap(visitType(_))).toSet

  /**
    * Emits flow constraints for all case field types in `enumDecl`.
    */
  private def visitRestrictableEnum(enumDecl: TypedAst.RestrictableEnum)(implicit ctx: Context): Set[Flow] =
    enumDecl.cases.values.flatMap(cas => cas.tpes.flatMap(visitType(_))).toSet

  /**
    * Emits flow constraints for all field types in `structDecl`.
    */
  private def visitStruct(structDecl: TypedAst.Struct)(implicit ctx: Context): Set[Flow] =
    structDecl.fields.values.flatMap(field => visitType(field.tpe)).toSet

  /**
    * Emits flow constraints for the formal parameter types, return type, and body of `defn`.
    */
  private def visitDef(defn: TypedAst.Def)(implicit ctx: Context): Set[Flow] =
    defn.spec.fparams.flatMap { case FormalParam(_, tpe, _, _, _) => visitType(tpe) }.toSet ++
    visitType(defn.spec.retTpe) ++
    visitExp(defn.exp)

  /**
    * Emits flow constraints for all call sites and enum usages in `exp`.
    *
    * Scope: all TypedAst expression forms are covered. Datalog fixpoint nodes
    * are handled structurally (sub-expression recursion only) — they do not yet
    * emit the Box/Unbox/liftN constraints required by Approach A; that is
    * deferred until the full Datalog handling design is implemented.
    * Channel nodes (NewChannel, GetChannel, etc.) are also structural only;
    * correct constraints for the synthesized stdlib calls require pre-lowering.
    */
  private def visitExp(exp: Expr)(implicit ctx: Context): Set[Flow] = exp match {
    case Expr.Cst(_, _, _) => Set.empty
    case Expr.Var(_, _, _) => Set.empty
    case Expr.Hole(_, _, _, _, _) => Set.empty

    case Expr.ApplyDef(symUse, exps, targs, _, _, _, _, loc) =>
      exps.flatMap(visitExp).toSet +
        Flow(FlowInput.FlowArgs(targs.map(typeToMonoArg(_, loc))), MVar.Def(symUse.sym))

    case Expr.ApplySig(symUse, exps, targ, targs, _, _, _, _, loc) =>
      exps.flatMap(visitExp).toSet +
        Flow(FlowInput.FlowArgs((targ :: targs).map(typeToMonoArg(_, loc))), MVar.Sig(symUse.sym))

    case Expr.ApplyOp(_, exps, _, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.ApplyClo(exp1, exp2, _, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Unary(_, exp, _, _, _) => visitExp(exp)

    case Expr.Binary(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Let(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Lambda(_, exp, _, _) => visitExp(exp)

    case Expr.IfThenElse(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.Stm(exps, exp, _, _, _) =>
      exps.flatMap(visitExp).toSet ++ visitExp(exp)

    case Expr.Discard(exp, _, _) => visitExp(exp)

    case Expr.Region(_, _, exp, _, _, _) => visitExp(exp)

    case Expr.Use(_, _, exp, _) => visitExp(exp)

    // Unlike the paper we don't annotate the match with the scrutinee enum type, because Flix
    // match rules do not carry a type-parameter annotation (as they do in LangPoly).
    case Expr.Match(exp, rules, _, _, _) =>
      visitExp(exp) ++ rules.flatMap {
        case MatchRule(_, guardOpt, body, _) =>
          guardOpt.map(visitExp).getOrElse(Set.empty) ++ visitExp(body)
      }.toSet

    case Expr.Tag(_, exps, tpe, _, loc) =>
      val (mvar, tpArgs) = getEnumMVarAndTypeArgs(tpe, loc)
      exps.flatMap(visitExp).toSet +
        Flow(FlowInput.FlowArgs(tpArgs.map(typeToMonoArg(_, loc))), mvar)

    case Expr.RestrictableTag(_, exps, tpe, _, loc) =>
      // PRE-LOWERING: pre-lowering will rewrite RestrictableTag to Tag over MVar.Enum.
      // Until then we emit MVar.RestrictableEnum — the solver will need to handle both.
      val (mvar, tpArgs) = getEnumMVarAndTypeArgs(tpe, loc)
      exps.flatMap(visitExp).toSet +
        Flow(FlowInput.FlowArgs(tpArgs.map(typeToMonoArg(_, loc))), mvar)

    case Expr.RestrictableChoose(_, exp, rules, _, _, _) =>
      // PRE-LOWERING: pre-lowering will rewrite RestrictableChoose to Match.
      // Until then we recurse structurally — correct since no new call sites are introduced.
      visitExp(exp) ++ rules.flatMap(r => visitExp(r.exp)).toSet

    case Expr.ExtMatch(exp, rules, _, _, _) =>
      visitExp(exp) ++ rules.flatMap(r => visitExp(r.exp)).toSet

    case Expr.ExtTag(_, exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.OpenAs(_, exp, _, _) => visitExp(exp)

    case Expr.Tuple(exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.LocalDef(_, bnd, _, exp1, exp2, _, _, _) =>
      visitType(bnd.tpe) ++ visitExp(exp1) ++ visitExp(exp2)

    case Expr.ApplyLocalDef(_, exps, _, _, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.HoleWithExp(exp, _, _, _, _) => visitExp(exp)

    case Expr.RecordSelect(exp, _, _, _, _) => visitExp(exp)

    case Expr.RecordExtend(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.RecordRestrict(_, exp, _, _, _) => visitExp(exp)

    case Expr.ArrayLit(exps, exp, _, _, _) =>
      exps.flatMap(visitExp).toSet ++ visitExp(exp)

    case Expr.ArrayNew(exp1, exp2, exp3, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.ArrayLoad(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.ArrayLength(exp, _, _) => visitExp(exp)

    case Expr.ArrayStore(exp1, exp2, exp3, _, _) =>
      visitExp(exp1) ++ visitExp(exp2) ++ visitExp(exp3)

    case Expr.VectorLit(exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.VectorLoad(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.VectorLength(exp, _) => visitExp(exp)

    case Expr.StructNew(_, fields, region, _, _, _) =>
      fields.flatMap { case (_, e) => visitExp(e) }.toSet ++
        region.map(visitExp).getOrElse(Set.empty)

    case Expr.StructGet(exp, _, _, _, _) => visitExp(exp)

    case Expr.StructPut(exp1, _, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Lazy(exp, _, _) => visitExp(exp)

    case Expr.Force(exp, _, _, _) => visitExp(exp)

    case Expr.Ascribe(exp, _, _, _, _, _) => visitExp(exp)

    case Expr.InstanceOf(exp, _, _) => visitExp(exp)

    case Expr.CheckedCast(_, exp, _, _, _) => visitExp(exp)

    case Expr.UncheckedCast(exp, _, _, _, _, _) => visitExp(exp)

    case Expr.Unsafe(exp, _, _, _, _, _) => visitExp(exp)

    case Expr.TryCatch(exp, rules, _, _, _) =>
      visitExp(exp) ++ rules.flatMap(r => visitExp(r.exp)).toSet

    case Expr.Throw(exp, _, _, _) => visitExp(exp)

    case Expr.Handler(_, rules, _, _, _, _, _) =>
      rules.flatMap(r => visitExp(r.exp)).toSet

    case Expr.RunWith(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.Spawn(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.ParYield(frags, exp, _, _, _) =>
      frags.flatMap(f => visitExp(f.exp)).toSet ++ visitExp(exp)

    case Expr.InvokeConstructor(_, exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.InvokeSuperConstructor(_, exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.InvokeMethod(_, exp, exps, _, _, _) =>
      visitExp(exp) ++ exps.flatMap(visitExp).toSet

    case Expr.InvokeSuperMethod(_, exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.InvokeStaticMethod(_, exps, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.GetField(_, exp, _, _, _) => visitExp(exp)

    case Expr.PutField(_, exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.GetStaticField(_, _, _, _) => Set.empty

    case Expr.PutStaticField(_, exp, _, _, _) => visitExp(exp)

    case Expr.NewObject(_, _, _, _, constructors, methods, _) =>
      constructors.flatMap(c => visitExp(c.exp)).toSet ++
        methods.flatMap(m => visitExp(m.exp)).toSet

    // PRE-LOWERING: NewChannel/GetChannel/PutChannel/SelectChannel must be handled by
    // pre-lowering. Each node desugars to one or more ApplyDef calls to polymorphic
    // stdlib defs (ChannelNewTuple, ChannelGet, ChannelPut, ChannelMpmcAdmin,
    // ChannelSelectFrom, ChannelUnsafeGetAndUnlock). Without pre-lowering those call
    // sites are invisible here and the corresponding Flow constraints are never emitted.
    // Until then we only recurse into sub-expressions so nested defs are still captured.
    case Expr.NewChannel(exp, _, _, _) => visitExp(exp)

    case Expr.GetChannel(exp, _, _, _) => visitExp(exp)

    case Expr.PutChannel(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.SelectChannel(rules, default, _, _, _) =>
      rules.flatMap(r => visitExp(r.chan) ++ visitExp(r.exp)).toSet ++
        default.map(visitExp).getOrElse(Set.empty)

    // Datalog fixpoint nodes: sub-expressions are traversed so that any defs
    // called inside predicates are captured, but the Box/Unbox/liftN constraints
    // are NOT emitted here. Those require Approach A (see lowering_design.md).
    case Expr.FixpointConstraintSet(cs, _, _) =>
      cs.flatMap { c =>
        val fromHead = c.head match {
          case Predicate.Head.Atom(_, _, terms, _, _) => terms.flatMap(visitExp).toSet
        }
        val fromBody = c.body.flatMap {
          case Predicate.Body.Guard(e, _)        => visitExp(e)
          case Predicate.Body.Functional(_, e, _) => visitExp(e)
          case _: Predicate.Body.Atom             => Set.empty
        }.toSet
        fromHead ++ fromBody
      }.toSet

    case Expr.FixpointLambda(_, exp, _, _, _) => visitExp(exp)

    case Expr.FixpointMerge(exp1, exp2, _, _, _) =>
      visitExp(exp1) ++ visitExp(exp2)

    case Expr.FixpointSolveWithProject(exps, _, _, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.FixpointInjectInto(exps, _, _, _, _) =>
      exps.flatMap(visitExp).toSet

    case Expr.FixpointQueryWithSelect(exps, queryExp, selects, from, where, _, _, _, _) =>
      exps.flatMap(visitExp).toSet ++
        visitExp(queryExp) ++
        selects.flatMap(visitExp).toSet ++
        from.flatMap {
          case Predicate.Body.Guard(e, _)        => visitExp(e)
          case Predicate.Body.Functional(_, e, _) => visitExp(e)
          case _: Predicate.Body.Atom             => Set.empty
        }.toSet ++
        where.flatMap(visitExp).toSet

    case Expr.FixpointQueryWithProvenance(exps, select, _, _, _, _) =>
      exps.flatMap(visitExp).toSet ++ (select match {
        case Predicate.Head.Atom(_, _, terms, _, _) => terms.flatMap(visitExp).toSet
      })

    case Expr.Error(_, _, _) => Set.empty
  }


  /**
    * Flattens a chain of Type.Apply to find the root type constructor head.
    */
  private def getAppHead(tpe: Type): Type = tpe match {
    case Type.Apply(t1, _, _) => getAppHead(t1)
    case head => head
  }

  /**
    * Unrolls a chain of Type.Apply to collect all applied type arguments in order.
    */
  private def getAppArgs(tpe: Type): List[Type] = tpe match {
    case Type.Apply(t1, t2, _) => getAppArgs(t1) :+ t2
    case _ => Nil
  }

  /**
    * Converts `tpe` to a `MonoArg` relative to the current declaration context.
    * Type variables bound by the current declaration become `Param`; everything else becomes `Const` or `App`.
    */
  private def typeToMonoArg(tpe: Type, loc: SourceLocation)(implicit ctx: Context): MonoArg = tpe match {
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
    case Type.AssocType(symUse, arg, _, _) =>
      // Ground: resolve eagerly. Non-ground: record symbolically for the solver.
      if (tpe.typeVars.isEmpty) MonoArg.Const(reduceAssocType(tpe))
      else MonoArg.Assoc(symUse.sym, typeToMonoArg(arg, loc))
    case Type.Cst(_, _) | _: Type.BaseType =>
      MonoArg.Const(tpe)
    case Type.Apply(_, _, loc) =>
      if (tpe.kind == Kind.Eff && tpe.typeVars.isEmpty)
        MonoArg.Const(canonicalEffect(tpe))
      else
        MonoArg.App(getAppHead(tpe), getAppArgs(tpe).map(arg => typeToMonoArg(arg, loc)))
    case other =>
      MonoArg.Const(other)
  }

  /** Returns the enum `MVar` and type arguments for a fully-applied enum type. */
  private def getEnumMVarAndTypeArgs(tpe: Type, loc: SourceLocation): (MVar, List[Type]) =
    getAppHead(tpe) match {
      case Type.Cst(TypeConstructor.Enum(sym, _), _)             => (MVar.Enum(sym), getAppArgs(tpe))
      case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) => (MVar.RestrictableEnum(sym), getAppArgs(tpe))
      case _ => throw InternalCompilerException(s"ConstraintGen: bad types? ${tpe}", loc)
    }

  /** Reduces a ground associated type to its concrete type via the EqualityEnv. */
  private def reduceAssocType(assoc: Type)(implicit ctx: Context): Type = {
    val progress = Progress()
    val (res, cs) = TypeReduction2.reduce(assoc)(RegionScope.Top, RigidityEnv.empty, progress, ctx.root.eqEnv, ctx.flix)
    if (cs.nonEmpty) throw InternalCompilerException(s"unexpected constraints: $cs", assoc.loc)
    if (progress.query()) res
    else throw InternalCompilerException(s"Could not reduce associated type $assoc", assoc.loc)
  }

  // TODO: canonicalEffect, evalEffect, and coSetToType are duplicated from Specialization.scala.
  //       They should be extracted into a shared utility (e.g. MonomorphUtils.scala) since the
  //       constraint solver will also need to normalize ground effect types after substitution.

  /** Returns the canonical form of the ground effect type `eff`. */
  private def canonicalEffect(eff: Type): Type =
    coSetToType(evalEffect(eff), eff.loc)

  /**
    * Evaluates the ground effect `eff` to a set of effect symbols.
    *
    * N.B.: `eff` must be ground (no free type variables).
    */
  private def evalEffect(eff: Type): CofiniteSet[Symbol.EffSym] = eff match {
    case Type.Univ                                                                      => CofiniteSet.universe
    case Type.Pure                                                                      => CofiniteSet.empty
    case Type.Cst(TypeConstructor.Effect(sym, _), _)                                    => CofiniteSet.mkSet(sym)
    case Type.Cst(TypeConstructor.Region(_), _)                                         => CofiniteSet.mkSet(Symbol.IO)
    case Type.Apply(Type.Cst(TypeConstructor.Complement, _), y, _)                      => CofiniteSet.complement(evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Union, _), x, _), y, _)         => CofiniteSet.union(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Intersection, _), x, _), y, _)  => CofiniteSet.intersection(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.Difference, _), x, _), y, _)    => CofiniteSet.difference(evalEffect(x), evalEffect(y))
    case Type.Apply(Type.Apply(Type.Cst(TypeConstructor.SymmetricDiff, _), x, _), y, _) => CofiniteSet.xor(evalEffect(x), evalEffect(y))
    case other => throw InternalCompilerException(s"Unexpected effect $other", other.loc)
  }

  /** Returns the [[Type]] representation of `set` at `loc`. */
  private def coSetToType(set: CofiniteSet[Symbol.EffSym], loc: SourceLocation): Type = set match {
    case CofiniteSet.Set(s)   => Type.mkUnion(s.toList.map(sym => Type.Cst(TypeConstructor.Effect(sym, Kind.Eff), loc)), loc)
    case CofiniteSet.Compl(s) => Type.mkComplement(Type.mkUnion(s.toList.map(sym => Type.Cst(TypeConstructor.Effect(sym, Kind.Eff), loc)), loc), loc)
  }
}
