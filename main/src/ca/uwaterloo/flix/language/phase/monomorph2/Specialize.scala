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
import ca.uwaterloo.flix.language.phase.typer.ConstraintSolver2
import ca.uwaterloo.flix.language.phase.unification.Substitution
import ca.uwaterloo.flix.util.collection.MapOps
import ca.uwaterloo.flix.util.{InternalCompilerException, ParOps}

import java.util.concurrent.ConcurrentLinkedQueue
import scala.jdk.CollectionConverters.*

/**
  * Solution-driven specialization: uses the solver's solution to specialize all def/enum/struct/
  * restrictable-enum in a single parallel pass.
  *
  * `run` is the entry point and owns the `SharedContext` lookup tables (`defTable`/`enumTable`/
  * `structTable`). The per-def specialize+lower walk itself lives in [[SpecializeAndLower.visitDef]],
  * which calls back into `lookupSym`/`lookupCaseSym`/`lookupStructSym`/`resolveSigSym` here to
  * resolve each call/tag/struct site.
  */
object Specialize {

  /**
    * Accumulates specialized defs; unlike `Specialization.SharedContext` there is no work queue, since
    * every specialization is known upfront from the solver solution.
    *
    * `defTable` maps (original sym, instantiated arrow type) → fresh specialized sym.
    * `enumTable`/`structTable`/`restrictableEnumTable` mirror it for enums/structs/restrictable
    * enums, keyed by (original sym, ground type-arg tuple) — see
    * `lookupCaseSym`/`lookupStructSym`/`lookupRestrictableCaseSym`. `restrictableEnumTable` maps
    * to a regular `EnumSym`: restrictable enums lower to regular enums (the restriction itself is
    * erased, checking already concluded), so they need no fresh-symbol infrastructure of their own.
    *
    * Package-visible: [[SpecializeAndLower]] needs it as the type its `sctx` implicit is threaded
    * through.
    */
  private[monomorph2] class SharedContext(
    val defTable: Map[(Symbol.DefnSym, Type), Symbol.DefnSym],
    val allDefs: Map[Symbol.DefnSym, TypedAst.Def],
    val enumTable: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym],
    val structTable: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym],
    val restrictableEnumTable: Map[(Symbol.RestrictableEnumSym, List[Type]), Symbol.EnumSym],
    // Carried here (rather than as a separate implicit threaded through every [[SpecializeAndLower]]
    // helper) solely for the fused walk's ApplySig case, which calls resolveSigSym.
    val instances: Map[(Symbol.TraitSym, TypeConstructor), Instance]
  ) {
    private val specializedDefs: ConcurrentLinkedQueue[(Symbol.DefnSym, MonoAst.Def)] = new ConcurrentLinkedQueue()

    /** Records `defn` under its fresh specialized `sym`. */
    def addSpecializedDef(sym: Symbol.DefnSym, defn: MonoAst.Def): Unit =
      specializedDefs.add((sym, defn))

    /** Returns all specialized defs recorded so far. */
    def getSpecializedDefs: Map[Symbol.DefnSym, MonoAst.Def] =
      specializedDefs.asScala.toMap

    // Diagnostic only, for `MonomorphBench`'s `Xmonobench` table: which of "regularDefs"/
    // "instanceDefs"/"defaultSigImpls" each specialized def came from.
    private val defCategoryCounts: ConcurrentLinkedQueue[String] = new ConcurrentLinkedQueue()

    /** Increments the count for `category` (one of "regularDefs"/"instanceDefs"/"defaultSigImpls"). */
    def incrementDefCategory(category: String): Unit =
      defCategoryCounts.add(category)

    /** Returns the per-category specialized-def counts. */
    def getDefCategoryCounts: Map[String, Int] =
      defCategoryCounts.asScala.groupMapReduce(identity)(_ => 1)(_ + _)
  }

  /**
    * Returns the sym to use for a call to `sym` instantiated at `it`.
    * - Non-parametric defs: keep the original sym.
    * - Parametric defs: must be in `defTable` (pre-populated from the solver solution); a miss
    *   crashes with "Solver gap", identifying a constraint-generator gap.
    *
    * Package-visible: [[SpecializeAndLower.lookup]] also calls this directly to resolve
    * lowering-synthesized calls (e.g. channel support functions).
    */
  private[monomorph2] def lookupSym(sym: Symbol.DefnSym, it: Type)
                       (implicit sctx: SharedContext): Symbol.DefnSym = {
    val defn = sctx.allDefs.getOrElse(sym, throw InternalCompilerException(s"lookupSym: sym not in allDefs: $sym", sym.loc))
    // Check defTable first: polymorphic instance defs and default-sig impls may have empty
    // spec.tparams but still need specialization (via instTparams / traitTparams).
    sctx.defTable.get((sym, it)) match {
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
    * - Missing entries: crash with "Solver gap" — ALWAYS, including `AnyType`-containing tuples:
    *   pattern-only instantiations are deliberately specialized at `AnyType` by
    *   `ConstraintCollection.visitPat` (see its ⚠️ doc comment), so no tolerance exists here.
    */
  private[monomorph2] def lookupCaseSym(caseSym: Symbol.CaseSym, groundEnumTpe: Type)(implicit sctx: SharedContext): Symbol.CaseSym = {
    val argTypes = groundEnumTpe.typeArguments
    sctx.enumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, caseSym.ordinal, caseSym.loc)
      case None if argTypes.isEmpty => caseSym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no enum specialization for ${caseSym.enumSym} at $argTypes. " +
          "Extend the constraint generator to cover this call site.", caseSym.loc)
    }
  }

  /**
    * Returns the (regular) case sym to use for a restrictable tag/pattern whose original
    * restrictable case is `caseSym` and whose ground restrictable-enum type at this expression
    * site is `groundEnumTpe`. Unlike `lookupCaseSym`, there is no "non-generic keeps original sym"
    * branch: a restrictable enum's type-argument list always starts with its case-set index
    * (`Kind.CaseSet`), so `argTypes` is never empty — every reference must be in the table.
    */
  private[monomorph2] def lookupRestrictableCaseSym(caseSym: Symbol.RestrictableCaseSym, groundEnumTpe: Type)(implicit sctx: SharedContext): Symbol.CaseSym = {
    val argTypes = groundEnumTpe.typeArguments
    sctx.restrictableEnumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, -1, caseSym.loc)
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no restrictable enum specialization for ${caseSym.enumSym} at $argTypes. " +
          "Extend the constraint generator to cover this call site.", caseSym.loc)
    }
  }

  /**
    * Returns the struct sym to use for a `StructNew`/`StructGet`/`StructPut` whose original
    * struct is `sym` and whose ground struct type at this expression site is `groundStructTpe`.
    * Same "non-generic keeps original / generic must be in `structTable` / miss is a Solver gap"
    * shape as `lookupCaseSym`.
    */
  private[monomorph2] def lookupStructSym(sym: Symbol.StructSym, groundStructTpe: Type)(implicit sctx: SharedContext): Symbol.StructSym = {
    val argTypes = groundStructTpe.typeArguments
    sctx.structTable.get((sym, argTypes)) match {
      case Some(freshStructSym) => freshStructSym
      case None if argTypes.isEmpty => sym
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no struct specialization for $sym at $argTypes. " +
          "Extend the constraint generator to cover this call site.", groundStructTpe.loc)
    }
  }

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
        case (sym, tpe) => sym -> Canonicalization.simplify(tpe.map(Canonicalization.default), isGround = true)
      }
      StrictSubstitution(Substitution(m))
    }
  }

  private[monomorph2] case class StrictSubstitution(s: Substitution) {
    /** Applies this substitution to `tpe0`, defaulting any free type variable to its kind's default type. */
    def apply(tpe0: Type)(implicit root: TypedAst.Root, flix: Flix): Type = tpe0 match {
      case v@Type.Var(sym, _) => s.m.get(sym) match {
        case None    => Canonicalization.default(v)
        case Some(t) => t
      }
      case Type.Cst(TypeConstructor.Region(_), loc) => Type.Cst(RegionInstantiation, loc)
      case cst@Type.Cst(_, _)                       => cst
      case app@Type.Apply(_, _, _)                  => Canonicalization.normalizeApply(apply, app, isGround = true)
      case Type.Alias(_, _, t, _)                   => apply(t)
      case Type.AssocType(symUse, arg0, kind, loc) =>
        val arg = apply(arg0)
        val assoc = Type.AssocType(symUse, arg, kind, loc)
        val reducedType = Canonicalization.reduceAssocType(assoc)
        Canonicalization.simplify(reducedType, isGround = true)
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
        TypedAst.StructField(fieldSym, Canonicalization.simplify(tpe, isGround = false), loc)
    }

  /** Simplifies the types embedded in `caze`. */
  private def visitEnumCase(caze: TypedAst.Case)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Case =
    caze match {
      case TypedAst.Case(sym, tpes, sc, loc) =>
        TypedAst.Case(sym, tpes.map(Canonicalization.simplify(_, isGround = false)), sc, loc)
    }

  /** Applies `StrictSubstitution.empty` to the types embedded in `op`. */
  private def visitEffectOp(op: TypedAst.Op)(implicit root: TypedAst.Root, flix: Flix): TypedAst.Op =
    op match {
      case TypedAst.Op(sym, TypedAst.Spec(doc, ann, mod, tparams, fparams0, declaredScheme, retTpe, eff, tconstrs, econstrs), loc) =>
        val fparams = fparams0.map {
          case TypedAst.FormalParam(varSym, tpe, src, decreasing, fpLoc) =>
            TypedAst.FormalParam(varSym, StrictSubstitution.empty(tpe), src, decreasing, fpLoc)
        }
        // declaredScheme.base needs the same canonicalization as fparams/retTpe/eff below — its
        // only consumer, [[SpecializeAndLower.lowerSpec]], feeds it straight into functionType, and an
        // un-canonicalized type doesn't structurally match enumTable/structTable's keys (built
        // from canonicalized tuples throughout), so rewriteEnumStructType silently misses.
        val canonScheme = declaredScheme.copy(base = StrictSubstitution.empty(declaredScheme.base))
        val spec = TypedAst.Spec(doc, ann, mod, tparams, fparams, canonScheme, StrictSubstitution.empty(retTpe), StrictSubstitution.empty(eff), tconstrs, econstrs)
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
    * Structurally rewrites `tpe`: any `Enum(sym, args)`/`Struct(sym, args)`/
    * `RestrictableEnum(sym, args)` sub-type whose `(sym, args)` pair is a key in
    * `sctx.enumTable`/`sctx.structTable`/`sctx.restrictableEnumTable` becomes `Enum(freshSym, Nil)`/
    * `Struct(freshSym, Nil)` (fully specialized, no more type arguments) — note a
    * `RestrictableEnum` reference becomes a plain `Enum` type too, since that table maps to a
    * regular `EnumSym`; anything else is left alone except for recursing into its own sub-parts
    * (which may themselves need rewriting, e.g. `List[Option[Int32]]` needs both `List` and
    * `Option` rewritten if both were specialized).
    *
    * Package-visible: [[SpecializeAndLower.visitType]] calls this inline at every type-construction
    * site in the fused walk (folding this rewrite into the same pass instead of a separate
    * post-pass over the whole tree).
    */
  private[monomorph2] def rewriteEnumStructType(tpe: Type)(implicit sctx: SharedContext): Type = tpe match {
    case Type.Apply(_, _, loc) =>
      val args = tpe.typeArguments
      tpe.baseType match {
        case Type.Cst(TypeConstructor.Enum(sym, _), _) if sctx.enumTable.contains((sym, args)) =>
          Type.mkEnum(sctx.enumTable((sym, args)), Nil, loc)
        case Type.Cst(TypeConstructor.RestrictableEnum(sym, _), _) if sctx.restrictableEnumTable.contains((sym, args)) =>
          Type.mkEnum(sctx.restrictableEnumTable((sym, args)), Nil, loc)
        case Type.Cst(TypeConstructor.Struct(sym, _), _) if sctx.structTable.contains((sym, args)) =>
          Type.mkStruct(sctx.structTable((sym, args)), Nil, loc)
        case _ =>
          Type.mkApply(rewriteEnumStructType(tpe.baseType), args.map(rewriteEnumStructType), loc)
      }
    case Type.Alias(sym, args, inner, loc) =>
      Type.Alias(sym, args.map(rewriteEnumStructType), rewriteEnumStructType(inner), loc)
    case _ => tpe // Var, other Cst, AssocType, etc. — nothing to rewrite.
  }

  /** Applies [[rewriteEnumStructType]] to every type embedded in `spec`. */
  private def rewriteSpec(spec: MonoAst.Spec)(implicit sctx: SharedContext): MonoAst.Spec =
    spec.copy(
      fparams = spec.fparams.map(rewriteFormalParam),
      functionType = rewriteEnumStructType(spec.functionType),
      retTpe = rewriteEnumStructType(spec.retTpe),
      eff = rewriteEnumStructType(spec.eff)
    )

  /**
    * Applies [[rewriteEnumStructType]] to `fp`'s type.
    *
    * Package-visible: [[SpecializeAndLower]]'s per-def walk calls this directly wherever it lowers an
    * already-specialized formal param.
    */
  private[monomorph2] def rewriteFormalParam(fp: MonoAst.FormalParam)(implicit sctx: SharedContext): MonoAst.FormalParam =
    fp.copy(tpe = rewriteEnumStructType(fp.tpe))

  /**
    * Applies [[rewriteEnumStructType]] to every op's `Spec` in `eff`.
    *
    * An op's `Spec` is lowered independently of any def body, so it never passes through
    * [[SpecializeAndLower.visitType]]'s inline rewrite; this explicit post-pass is what keeps it
    * consistent with `TypeVerifier`'s enumSym-matches-embedded-type invariant.
    */
  private def rewriteEffect(eff: MonoAst.Effect)(implicit sctx: SharedContext): MonoAst.Effect =
    eff.copy(ops = eff.ops.map(op => op.copy(spec = rewriteSpec(op.spec))))

  /** Specializes `root` per `solution`, the constraint solver's output from Phase 3. */
  def run(root: TypedAst.Root, solution: Solution)(implicit flix: Flix): MonoAst.Root = flix.phase("Monomorpher") {
    implicit val r: TypedAst.Root = root
    val is: Map[(Symbol.TraitSym, TypeConstructor), Instance] = MonomorphHelpers.mkInstanceMap(root.instances)

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
      root.sigs.values.flatMap {
        sig =>
          sig.exp.map {
            exp =>
              val ns      = sig.sym.trt.namespace :+ sig.sym.trt.name
              val defnSym = new Symbol.DefnSym(None, ns, sig.sym.name, sig.sym.loc)
              defnSym -> TypedAst.Def(defnSym, sig.spec, exp, sig.sym.loc)
          }
      }.toMap
    // Maps each default-sig-sym to the trait's own tparams (not in sig.spec.tparams).
    val defaultSigTraitTparams: Map[Symbol.DefnSym, List[TypedAst.TypeParam]] =
      root.sigs.values.flatMap {
        sig =>
          sig.exp.map {
            _ =>
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
        tuple          <- tuples
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
        tuple         <- tuples
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

    // Same shape as enumEntries, except: (a) the tuple is zipped against `index :: tparams` (the
    // case-set index is always the first solved type argument — see ConstraintCollection's
    // fromRestrictableEnums), and (b) the built declaration is an ordinary TypedAst.Enum, not a
    // TypedAst.RestrictableEnum — restrictable enums lower to regular enums, so their specialized
    // copies can go straight through the same [[SpecializeAndLower.lowerEnum]] as regular enums.
    val restrictableEnumEntries: List[(Symbol.RestrictableEnumSym, List[Type], Symbol.EnumSym, TypedAst.Enum)] =
      for {
        (sym, tuples) <- solution.restrictableEnums.toList
        enm           <- root.restrictableEnums.get(sym).toList
        tuple         <- tuples
        substMap       = (enm.index :: enm.tparams).zip(tuple).map { case (tp, ty) => tp.sym -> ty }.toMap
        freshSym       = Symbol.freshEnumSym(SpecializeAndLower.lowerRestrictableEnumSym(sym))
        subst         <- try {
                           List(StrictSubstitution.mk(Substitution(substMap)))
                         } catch {
                           case _: InternalCompilerException => Nil
                         }
      } yield {
        val newCases = enm.cases.map { case (caseSym, TypedAst.RestrictableCase(_, tpes, sc, cloc)) =>
          val newCaseSym = new Symbol.CaseSym(freshSym, caseSym.name, -1, caseSym.loc)
          newCaseSym -> TypedAst.Case(newCaseSym, tpes.map(subst.apply), sc, cloc)
        }
        (sym, tuple, freshSym, TypedAst.Enum(enm.doc, enm.ann, enm.mod, freshSym, Nil, enm.derives, newCases, enm.loc))
      }

    val restrictableEnumTableMap: Map[(Symbol.RestrictableEnumSym, List[Type]), Symbol.EnumSym] =
      restrictableEnumEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    val structEntries: List[(Symbol.StructSym, List[Type], Symbol.StructSym, TypedAst.Struct)] =
      for {
        (sym, tuples) <- solution.structs.toList
        struct        <- root.structs.get(sym).toList
        if struct.tparams.nonEmpty
        tuple         <- tuples
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

    implicit val sctx: SharedContext = new SharedContext(defTableMap, allDefs, enumTableMap, structTableMap, restrictableEnumTableMap, is)

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
        sctx.incrementDefCategory(if (defToInst.contains(sym)) "instanceDefs" else "regularDefs")
        sctx.addSpecializedDef(sym, SpecializeAndLower.visitDef(sym, defn, StrictSubstitution.empty))
      }
    }

    // Parametric specializations — one parallel pass, no worklist loop.
    ParOps.parMapWithPriority(entries, sortBy = (e: (Symbol.DefnSym, TypedAst.Def, StrictSubstitution, Type)) => sortBySize(e._2)) { case (freshSym, defn, subst, _) =>
      flix.profile(defn.sym, defn.loc) {
        val category =
          if (defToInst.contains(defn.sym)) "instanceDefs"
          else if (defaultSigDefs.contains(defn.sym)) "defaultSigImpls"
          else "regularDefs"
        sctx.incrementDefCategory(category)
        sctx.addSpecializedDef(freshSym, SpecializeAndLower.visitDef(freshSym, defn, subst))
      }
    }

    val effects = ParOps.parMapValues(root.effects) {
      case TypedAst.Effect(doc, ann, mod, sym, targs, ops0, loc) =>
        val ops = ops0.map(visitEffectOp)
        rewriteEffect(SpecializeAndLower.lowerEffect(TypedAst.Effect(doc, ann, mod, sym, targs, ops, loc)))
    }

    // Generic originals (tparams.nonEmpty) are dropped: every reachable instantiation already has
    // a specialized copy in enumEntries (built from the solver solution above), and every
    // construction/pattern site is routed there via the strict lookupCaseSym/lookupStructSym —
    // including [[SpecializeAndLower]]'s Datalog runtime enums (Fixpoint3.Ast.*, `FList`, `PredSym`,
    // `Denotation`), which are ordinary solver-predicted instantiations like any other. Only
    // non-parametric declarations keep their original sym, since they were never specialized in
    // the first place. Restrictable enums have no non-parametric case at all (their type-argument
    // list always starts with the case-set index) — see specializedRestrictableEnums below, which
    // replaces them the same way.
    val enums = ParOps.parMapValues(root.enums.filter { case (_, e) => e.tparams.isEmpty }) {
      case TypedAst.Enum(doc, ann, mod, sym, tparams, derives, cases, loc) =>
        SpecializeAndLower.lowerEnum(TypedAst.Enum(doc, ann, mod, sym, tparams, derives, MapOps.mapValues(cases)(visitEnumCase), loc))
    }

    // One specialized declaration (fresh sym, renamed cases, ground field types, tparams = Nil)
    // per (sym, tuple) the solver actually found reachable — see enumEntries above and
    // lookupCaseSym, which is what makes expressions actually reference these fresh syms.
    val specializedEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(enumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SpecializeAndLower.lowerEnum(newEnum) }.toMap

    // Same shape as specializedEnums, per restrictableEnumEntries — see lookupRestrictableCaseSym,
    // which is what makes Expr.RestrictableTag/RestrictableChoosePattern reference these fresh syms.
    val specializedRestrictableEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(restrictableEnumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SpecializeAndLower.lowerEnum(newEnum) }.toMap

    val structs = ParOps.parMapValues(root.structs.filter { case (_, s) => s.tparams.isEmpty }) {
      case TypedAst.Struct(doc, ann, mod, sym, tparams, sc, fields, loc) =>
        SpecializeAndLower.lowerStruct(TypedAst.Struct(doc, ann, mod, sym, tparams, sc, MapOps.mapValues(fields)(visitStructField), loc))
    }

    val specializedStructs: Map[Symbol.StructSym, MonoAst.Struct] =
      ParOps.parMap(structEntries) { case (_, _, freshSym, newStruct) => freshSym -> SpecializeAndLower.lowerStruct(newStruct) }.toMap

    // Diagnostic only (see SharedContext.defCategoryCounts) — no equivalent exists for the
    // demand-driven baseline (Specialization.scala), so MonomorphBench must treat this as
    // this-pipeline-only data, not something to expect from every run.
    flix.emitEvent(FlixEvent.AfterMonomorphCategories(sctx.getDefCategoryCounts))

    MonoAst.Root(
      sctx.getSpecializedDefs,
      enums ++ specializedEnums ++ specializedRestrictableEnums,
      structs ++ specializedStructs,
      effects,
      root.mainEntryPoint,
      root.entryPoints,
      root.sources
    )
  }
}
