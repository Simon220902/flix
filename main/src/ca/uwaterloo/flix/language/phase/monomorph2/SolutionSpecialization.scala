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

import ca.uwaterloo.flix.api.{Flix, FlixEvent}
import ca.uwaterloo.flix.language.ast.TypedAst.{Binder, Instance}
import ca.uwaterloo.flix.language.ast.shared.RegionScope
import ca.uwaterloo.flix.language.ast.{Kind, MonoAst, RigidityEnv, Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.language.dbg.AstPrinter.*
import ca.uwaterloo.flix.language.phase.monomorph2.ConstraintSolver.Solution
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.language.phase.unification.Substitution
import ca.uwaterloo.flix.util.collection.MapOps
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import scala.annotation.tailrec
import scala.collection.mutable

/**
  * Solution-driven specialization: uses the solver solution from Phase 3 to specialize all defs
  * in a single parallel pass, with no demand-driven fallback. Crashes on any call site not
  * covered by the solution ("solver gap"), which identifies missing constraints.
  *
  * `run` is the entry point and owns the `Context` lookup tables (`defTable`/`enumTable`/
  * `structTable`). The per-def specialize+lower walk itself lives in `[[SolutionLowering.visitDef]]`,
  * which calls back into `lookupSym`/`lookupCaseSym`/`lookupStructSym`/`resolveSigSym` here to
  * resolve each call/tag/struct site.
  */
object SolutionSpecialization {

  /**
    * Accumulates specialized defs; unlike `Specialization.Context` there is no work queue, since
    * every specialization is known upfront from the solver solution.
    *
    * `defTable` maps (original sym, instantiated arrow type) → fresh specialized sym.
    * `enumTable`/`structTable` mirror it for enums/structs, keyed by (original sym, ground
    * type-arg tuple) — see `lookupCaseSym`/`lookupStructSym`.
    *
    * Package-visible: `[[SolutionLowering]]` needs it as the type its `ctx` implicit is threaded
    * through.
    */
  private[monomorph2] class Context(
    val defTable: Map[(Symbol.DefnSym, Type), Symbol.DefnSym],
    val allDefs: Map[Symbol.DefnSym, TypedAst.Def],
    val enumTable: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym],
    val structTable: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym],
    // Carried here (rather than as a separate implicit threaded through every SolutionLowering
    // helper) solely for the fused walk's ApplySig case, which calls resolveSigSym.
    val instances: Map[(Symbol.TraitSym, TypeConstructor), Instance]
  ) {
    private val specializedDefs: mutable.Map[Symbol.DefnSym, MonoAst.Def] = mutable.Map.empty

    /** Records `defn` under its fresh specialized `sym`. */
    def addSpecializedDef(sym: Symbol.DefnSym, defn: MonoAst.Def): Unit =
      synchronized { specializedDefs.put(sym, defn) }

    /** Returns all specialized defs recorded so far. */
    def getSpecializedDefs: Map[Symbol.DefnSym, MonoAst.Def] =
      synchronized { specializedDefs.toMap }

    // Diagnostic only, for `MonomorphBench`'s `Xmonobench` table: which of "regularDefs"/
    // "instanceDefs"/"defaultSigImpls" each specialized def came from.
    private val defCategoryCounts: mutable.Map[String, Int] = mutable.Map.empty.withDefaultValue(0)

    /** Increments the count for `category` (one of "regularDefs"/"instanceDefs"/"defaultSigImpls"). */
    def incrementDefCategory(category: String): Unit =
      synchronized { defCategoryCounts(category) = defCategoryCounts(category) + 1 }

    /** Returns the per-category specialized-def counts. */
    def getDefCategoryCounts: Map[String, Int] = synchronized { defCategoryCounts.toMap }
  }

  /**
    * Returns the sym to use for a call to `sym` instantiated at `it`.
    * - Non-parametric defs: keep the original sym.
    * - Parametric defs: must be in `defTable` (pre-populated from the solver solution); a miss
    *   crashes with "Solver gap", identifying a constraint-generator gap.
    *
    * Package-visible: `SolutionLowering.lookup` also calls this directly to resolve
    * lowering-synthesized calls (e.g. channel support functions).
    */
  private[monomorph2] def lookupSym(sym: Symbol.DefnSym, it: Type)
                       (implicit ctx: Context): Symbol.DefnSym = {
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
    * - Generic enums: must be in `enumTable` (pre-populated from the solver solution).
    * - Missing entries: crash with "Solver gap", same failure mode as `lookupSym` — except for a
    *   dead-code `AnyType` default (`isAnyType`), which isn't a real gap (see its own doc comment).
    */
  private[monomorph2] def lookupCaseSym(caseSym: Symbol.CaseSym, groundEnumTpe: Type)(implicit ctx: Context): Symbol.CaseSym = {
    val argTypes = groundEnumTpe.typeArguments
    ctx.enumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, caseSym.ordinal, caseSym.loc)
      case None if argTypes.isEmpty || argTypes.exists(isAnyType) => caseSym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no enum specialization for ${caseSym.enumSym} at $argTypes. " +
          "Extend the constraint generator to cover this call site.", caseSym.loc)
    }
  }

  /**
    * True if `tpe` is (or contains) `AnyType` — the defaulted type `MonomorphCanon` assigns to a
    * stray, otherwise-unconstrained type var (e.g. an unreachable/dead pattern-match arm). A miss
    * against `enumTable`/`structTable` at such a type isn't a real "Solver gap": the constraint
    * generator never saw a real value constructed at this type because there isn't one — it's a
    * typechecking artifact, not code that runs. Keeping the original sym is the same fallback
    * already used for genuinely non-generic types.
    */
  private def isAnyType(tpe: Type): Boolean = tpe match {
    case Type.Cst(TypeConstructor.AnyType, _) => true
    case Type.Apply(t1, t2, _) => isAnyType(t1) || isAnyType(t2)
    case _ => false
  }

  /**
    * Returns the struct sym to use for a `StructNew`/`StructGet`/`StructPut` whose original
    * struct is `sym` and whose ground struct type at this expression site is `groundStructTpe`.
    * Same "non-generic keeps original / generic must be in `structTable` / miss is a Solver gap"
    * shape as `lookupCaseSym`.
    */
  private[monomorph2] def lookupStructSym(sym: Symbol.StructSym, groundStructTpe: Type)(implicit ctx: Context): Symbol.StructSym = {
    val argTypes = groundStructTpe.typeArguments
    ctx.structTable.get((sym, argTypes)) match {
      case Some(freshStructSym) => freshStructSym
      case None if argTypes.isEmpty || argTypes.exists(isAnyType) => sym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no struct specialization for $sym at $argTypes. " +
          "Extend the constraint generator to cover this call site.", groundStructTpe.loc)
    }
  }

  /**
    * Runs `lookup` (a `lookupCaseSym`/`lookupStructSym` call), falling back to `keep` if it
    * throws — used where a "Solver gap" miss doesn't necessarily mean a real constraint-generator
    * gap: post-lowering types don't always match the pre-lowering keys `enumTable`/`structTable`
    * were built from. Package-visible: `SolutionLowering.mkTag`, which synthesizes `Tag`
    * expressions outside the ordinary `Expr.Tag` rewrite path, is the sole caller.
    */
  private[monomorph2] def tolerant[A](lookup: => A, keep: => A): A =
    try lookup catch { case _: InternalCompilerException => keep }

  // StrictSubstitution and RegionInstantiation below are verbatim from Specialization.scala.

  /** The effect that all [[TypeConstructor.Region]] are instantiated to. */
  private val RegionInstantiation: TypeConstructor.Effect =
    TypeConstructor.Effect(Symbol.IO, Kind.Eff)

  private[monomorph2] object StrictSubstitution {
    /** The empty substitution. */
    val empty: StrictSubstitution = StrictSubstitution(Substitution.empty)

    /** Returns `s` as a [[StrictSubstitution]], with every type in its image simplified and grounded. */
    def mk(s: Substitution)(implicit root: TypedAst.Root, flix: Flix): StrictSubstitution = {
      val m = s.m.map {
        case (sym, tpe) => sym -> MonomorphCanon.simplify(tpe.map(MonomorphCanon.default), isGround = true)
      }
      StrictSubstitution(Substitution(m))
    }
  }

  private[monomorph2] case class StrictSubstitution(s: Substitution) {
    /** Applies this substitution to `tpe0`, defaulting any free type variable to its kind's default type. */
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

    /** Returns the non-strict version of this substitution. */
    def nonStrict: Substitution = s
  }

  // The helpers below are verbatim from Specialization.scala.

  /** Simplifies the types embedded in `field`. */
  private def visitStructField(field: TypedAst.StructField)(implicit root: TypedAst.Root, flix: Flix): TypedAst.StructField =
    field match {
      case TypedAst.StructField(fieldSym, tpe, loc) =>
        TypedAst.StructField(fieldSym, MonomorphCanon.simplify(tpe, isGround = false), loc)
    }

  /** Simplifies the types embedded in `caze`. */
  private def visitEnumCase(caze: TypedAst.Case)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Case =
    caze match {
      case TypedAst.Case(sym, tpes, sc, loc) =>
        TypedAst.Case(sym, tpes.map(MonomorphCanon.simplify(_, isGround = false)), sc, loc)
    }

  /** Simplifies the types embedded in `caze`. */
  private def visitRestrictableEnumCase(caze: TypedAst.RestrictableCase)(implicit root: TypedAst.Root, flix: Flix): TypedAst.RestrictableCase =
    caze match {
      case TypedAst.RestrictableCase(caseSym0, tpes, sc, loc) =>
        TypedAst.RestrictableCase(caseSym0, tpes.map(MonomorphCanon.simplify(_, isGround = false)), sc, loc)
    }

  /** Applies `StrictSubstitution.empty` to the types embedded in `op`. */
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

  /** Returns the `def` that implements signature `sym` for the instance at `tpe`, or its trait-level default. */
  private[monomorph2] def resolveSigSym(sym: Symbol.SigSym, tpe: Type)
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

  /** Merges `envs` into a single var-sym renaming map. */
  private def combineEnvs(envs: Iterable[Map[Symbol.VarSym, Symbol.VarSym]]): Map[Symbol.VarSym, Symbol.VarSym] =
    envs.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym])(_ ++ _)

  /** Specializes `fparams0` under `subst0`, returning the fresh params and the old-to-fresh var-sym renaming. */
  private[monomorph2] def specializeFormalParams(fparams0: List[TypedAst.FormalParam], subst0: StrictSubstitution)
                                     (implicit root: TypedAst.Root, flix: Flix): (List[TypedAst.FormalParam], Map[Symbol.VarSym, Symbol.VarSym]) = {
    val (params, envs) = fparams0.map(specializeFormalParam(_, subst0)).unzip
    (params, combineEnvs(envs))
  }

  /** Specializes `fparam0` under `subst0`, returning the fresh param and its old-to-fresh var-sym renaming. */
  private[monomorph2] def specializeFormalParam(fparam0: TypedAst.FormalParam, subst0: StrictSubstitution)
                                    (implicit root: TypedAst.Root, flix: Flix): (TypedAst.FormalParam, Map[Symbol.VarSym, Symbol.VarSym]) = {
    val TypedAst.FormalParam(bnd, tpe, src, decreasing, loc) = fparam0
    val freshSym = Symbol.freshVarSym(bnd.sym)
    (TypedAst.FormalParam(Binder(freshSym, subst0(bnd.tpe)), subst0(tpe), src, decreasing, loc), Map(bnd.sym -> freshSym))
  }

  // `lookupCaseSym`/`lookupStructSym` only rewrite the *symbol* on Tag/Is/Untag/StructNew/
  // StructGet/StructPut. Every other `Type` value in the tree still refers to the *original*
  // enum/struct sym with concrete type args, since `StrictSubstitution` only substitutes and
  // canonicalizes — it has no notion of fresh specialized syms. `TypeVerifier` asserts that a
  // Tag/Is/Untag's case-sym's `enumSym` matches the enum sym embedded in the surrounding type, so
  // `rewriteEnumStructType` below must rewrite the type everywhere it appears. It must run after
  // `lookupCaseSym`/`lookupStructSym` build their lookup keys from the raw type, or the lookup
  // keys would themselves already be rewritten and never match.

  /**
    * Structurally rewrites `tpe`: any `Enum(sym, args)`/`Struct(sym, args)` sub-type whose
    * `(sym, args)` pair is a key in `ctx.enumTable`/`structTable` becomes `Enum(freshSym, Nil)`/
    * `Struct(freshSym, Nil)` (fully specialized, no more type arguments); anything else is left
    * alone except for recursing into its own sub-parts (which may themselves need rewriting,
    * e.g. `List[Option[Int32]]` needs both `List` and `Option` rewritten if both were specialized).
    *
    * Package-visible: `SolutionLowering.visitType` calls this inline at every type-construction
    * site in the fused walk (folding this rewrite into the same pass instead of a separate
    * post-pass over the whole tree).
    */
  private[monomorph2] def rewriteEnumStructType(tpe: Type)(implicit ctx: Context): Type = tpe match {
    case Type.Apply(_, _, loc) =>
      val (head, args) = flattenApply(tpe)
      head match {
        case Type.Cst(TypeConstructor.Enum(sym, _), _) if ctx.enumTable.contains((sym, args)) =>
          Type.mkEnum(ctx.enumTable((sym, args)), Nil, loc)
        case Type.Cst(TypeConstructor.Struct(sym, _), _) if ctx.structTable.contains((sym, args)) =>
          Type.mkStruct(ctx.structTable((sym, args)), Nil, loc)
        case _ =>
          args.foldLeft(rewriteEnumStructType(head)) { case (acc, arg) => Type.Apply(acc, rewriteEnumStructType(arg), loc) }
      }
    case Type.Alias(sym, args, inner, loc) =>
      Type.Alias(sym, args.map(rewriteEnumStructType), rewriteEnumStructType(inner), loc)
    case _ => tpe // Var, other Cst, AssocType, etc. — nothing to rewrite.
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

  /** Applies [[rewriteEnumStructType]] to every type embedded in `spec`. */
  private def rewriteSpec(spec: MonoAst.Spec)(implicit ctx: Context): MonoAst.Spec =
    spec.copy(
      fparams = spec.fparams.map(rewriteFormalParam),
      functionType = rewriteEnumStructType(spec.functionType),
      retTpe = rewriteEnumStructType(spec.retTpe),
      eff = rewriteEnumStructType(spec.eff)
    )

  /**
    * Applies [[rewriteEnumStructType]] to `fp`'s type.
    *
    * Package-visible: `SolutionLowering`'s per-def walk calls this directly wherever it lowers an
    * already-specialized formal param.
    */
  private[monomorph2] def rewriteFormalParam(fp: MonoAst.FormalParam)(implicit ctx: Context): MonoAst.FormalParam =
    fp.copy(tpe = rewriteEnumStructType(fp.tpe))

  /**
    * Applies [[rewriteEnumStructType]] to every op's `Spec` in `eff`.
    *
    * An op's `Spec` is lowered independently of any def body, so it never passes through
    * `SolutionLowering.visitType`'s inline rewrite; this explicit post-pass is what keeps it
    * consistent with `TypeVerifier`'s enumSym-matches-embedded-type invariant.
    */
  private def rewriteEffect(eff: MonoAst.Effect)(implicit ctx: Context): MonoAst.Effect =
    eff.copy(ops = eff.ops.map(op => op.copy(spec = rewriteSpec(op.spec))))

  /** Specializes `root` per `solution`, the constraint solver's output from Phase 3. */
  def run(root: TypedAst.Root, solution: Solution)(implicit flix: Flix): MonoAst.Root = flix.phase("Monomorpher") {
    implicit val r: TypedAst.Root = root
    val is: Map[(Symbol.TraitSym, TypeConstructor), Instance] = MonomorphCanon.mkInstanceMap(root.instances)

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
    // Much simpler than defs' entries above: no instance-tparam-prefix / default-sig-tparam
    // complexity, just the declaration's own tparams zipped with the solved tuple. Same
    // speculative-tuple tolerance as defs (drop on InternalCompilerException rather than crash
    // the whole computation) for consistency, even though it's less likely to matter here (enum
    // case field types rarely carry trait constraints the way def signatures do).
    val enumEntries: List[(Symbol.EnumSym, List[Type], Symbol.EnumSym, TypedAst.Enum)] =
      for {
        (sym, tuples) <- solution.enums.toList
        enm           <- root.enums.get(sym).toList
        if enm.tparams.nonEmpty
        tuple         <- tuples.toList
        substMap       = enm.tparams.zip(tuple).map { case (tp, ty) => tp.sym -> ty }.toMap
        freshSym       = Symbol.freshEnumSym(enm.sym)
        subst         <- try {
                           List(StrictSubstitution.mk(Substitution(substMap)))
                         } catch {
                           case _: InternalCompilerException => Nil
                         }
      } yield {
        val newCases = enm.cases.map { case (caseSym, TypedAst.Case(_, tpes, sc, cloc)) =>
          val newCaseSym = new Symbol.CaseSym(freshSym, caseSym.name, caseSym.ordinal, caseSym.loc)
          newCaseSym -> TypedAst.Case(newCaseSym, tpes.map(subst.apply), sc, cloc)
        }
        (sym, tuple, freshSym, TypedAst.Enum(enm.doc, enm.ann, enm.mod, freshSym, Nil, enm.derives, newCases, enm.loc))
      }

    val enumTableMap: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym] =
      enumEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    val structEntries: List[(Symbol.StructSym, List[Type], Symbol.StructSym, TypedAst.Struct)] =
      for {
        (sym, tuples) <- solution.structs.toList
        struct        <- root.structs.get(sym).toList
        if struct.tparams.nonEmpty
        tuple         <- tuples.toList
        substMap       = struct.tparams.zip(tuple).map { case (tp, ty) => tp.sym -> ty }.toMap
        freshSym       = Symbol.freshStructSym(struct.sym)
        subst         <- try {
                           List(StrictSubstitution.mk(Substitution(substMap)))
                         } catch {
                           case _: InternalCompilerException => Nil
                         }
      } yield {
        val newFields = struct.fields.map { case (fieldSym, TypedAst.StructField(_, tpe, floc)) =>
          val newFieldSym = new Symbol.StructFieldSym(freshSym, fieldSym.name, fieldSym.loc)
          newFieldSym -> TypedAst.StructField(newFieldSym, subst(tpe), floc)
        }
        (sym, tuple, freshSym, TypedAst.Struct(struct.doc, struct.ann, struct.mod, freshSym, Nil, struct.sc, newFields, struct.loc))
      }

    val structTableMap: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym] =
      structEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    implicit val ctx: Context = new Context(defTableMap, allDefs, enumTableMap, structTableMap, is)

    // Biggest-first scheduling (same convention as Typer.scala/Lexer.scala/Weeder2.scala/
    // Parser2.scala's ParOps.*WithPriority uses): starting the largest defs' work first reduces
    // the long-tail straggler effect where most threads finish their small defs early and idle
    // while one thread grinds through whatever big def happened to be scheduled last.
    def sortBySize(defn: TypedAst.Def): Int = defn.loc.startLine - defn.loc.endLine

    // Non-parametric defs: those with no spec.tparams AND no instance tparams AND not a
    // default-sig impl (which has trait tparams not in spec.tparams — always goes via entries).
    ParOps.parMapWithPriority(allDefs.filter { case (sym, d) =>
      d.spec.tparams.isEmpty &&
      defToInst.get(sym).map(_.tparams.isEmpty).getOrElse(true) &&
      !defaultSigDefs.contains(sym)
    }, sortBy = (p: (Symbol.DefnSym, TypedAst.Def)) => sortBySize(p._2)) {
      case (sym, defn) => flix.profile(defn.sym, defn.loc) {
        ctx.incrementDefCategory(if (defToInst.contains(sym)) "instanceDefs" else "regularDefs")
        ctx.addSpecializedDef(sym, SolutionLowering.visitDef(sym, defn, StrictSubstitution.empty))
      }
    }

    // Parametric specializations — one parallel pass, no worklist loop.
    ParOps.parMapWithPriority(entries, sortBy = (e: (Symbol.DefnSym, TypedAst.Def, StrictSubstitution, Type)) => sortBySize(e._2)) { case (freshSym, defn, subst, _) =>
      flix.profile(defn.sym, defn.loc) {
        val category =
          if (defToInst.contains(defn.sym)) "instanceDefs"
          else if (defaultSigDefs.contains(defn.sym)) "defaultSigImpls"
          else "regularDefs"
        ctx.incrementDefCategory(category)
        ctx.addSpecializedDef(freshSym, SolutionLowering.visitDef(freshSym, defn, subst))
      }
    }

    val effects = ParOps.parMapValues(root.effects) {
      case TypedAst.Effect(doc, ann, mod, sym, targs, ops0, loc) =>
        val ops = ops0.map(visitEffectOp)
        rewriteEffect(SolutionLowering.lowerEffect(TypedAst.Effect(doc, ann, mod, sym, targs, ops, loc)))
    }

    // Original enum/struct declarations are all kept alongside the specialized ones below, never
    // replaced. Needed because: (a) SolutionLowering synthesizes MonoAst constructions (Datalog
    // runtime enums such as Fixpoint3.Ast.*, `FList`, `PredSym`, `Denotation`) that reference
    // original syms and bypass the Expr.Tag/StructNew rewrite; (b) non-parametric enums/structs
    // keep their original syms; (c) restrictable enums stay on their original (lowered) syms.
    // Nothing downstream prunes unused enum/struct declarations — MonomorphTreeShaker only prunes
    // defs/instances/sigs, and runs before this phase — so genuinely-unused originals currently
    // survive to codegen; pruning them is a known follow-up.
    val enums = ParOps.parMapValues(root.enums) {
      case TypedAst.Enum(doc, ann, mod, sym, tparams, derives, cases, loc) =>
        SolutionLowering.lowerEnum(TypedAst.Enum(doc, ann, mod, sym, tparams, derives, MapOps.mapValues(cases)(visitEnumCase), loc))
    }

    // One specialized declaration (fresh sym, renamed cases, ground field types, tparams = Nil)
    // per (sym, tuple) the solver actually found reachable — see enumEntries above and
    // lookupCaseSym, which is what makes expressions actually reference these fresh syms.
    val specializedEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(enumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SolutionLowering.lowerEnum(newEnum) }.toMap

    val restrictableEnums = ParOps.parMapValues(root.restrictableEnums) {
      case TypedAst.RestrictableEnum(doc, ann, mod, sym, index, tparams, derives, cases, loc) =>
        SolutionLowering.lowerRestrictableEnum(TypedAst.RestrictableEnum(doc, ann, mod, sym, index, tparams, derives, MapOps.mapValues(cases)(visitRestrictableEnumCase), loc))
    }

    val structs = ParOps.parMapValues(root.structs) {
      case TypedAst.Struct(doc, ann, mod, sym, tparams, sc, fields, loc) =>
        SolutionLowering.lowerStruct(TypedAst.Struct(doc, ann, mod, sym, tparams, sc, MapOps.mapValues(fields)(visitStructField), loc))
    }

    val specializedStructs: Map[Symbol.StructSym, MonoAst.Struct] =
      ParOps.parMap(structEntries) { case (_, _, freshSym, newStruct) => freshSym -> SolutionLowering.lowerStruct(newStruct) }.toMap

    // Diagnostic only (see Context.defCategoryCounts) — no equivalent exists for the
    // demand-driven baseline (Specialization.scala), so MonomorphBench must treat this as
    // this-pipeline-only data, not something to expect from every run.
    flix.emitEvent(FlixEvent.AfterMonomorphCategories(ctx.getDefCategoryCounts))

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
