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
  * Solution-driven specialization uses [[ConstraintSolver]]'s solution to specialize every def/enum/
  * struct/restrictable-enum in a single parallel pass.
  *
  * `run` builds the `SharedContext` lookup tables.
  *
  * [[SpecializeAndLower.visitDef]] does the actual per-def specialize+lower walk, resolving each
  * call/tag/struct site via `lookupSym`/`lookupCaseSym`/`lookupRestrictableCaseSym`/
  * `lookupStructSym`/`resolveSigSym`.
  */
object Specialize {

  /**
    * The mutable data used throughout specialization.
    *
    * This class is thread-safe.
    */
  private[monomorph2] class SharedContext(
    val defTable: Map[(Symbol.DefnSym, Type), Symbol.DefnSym],
    val allDefs: Map[Symbol.DefnSym, TypedAst.Def],
    val enumTable: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym],
    val structTable: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym],
    val restrictableEnumTable: Map[(Symbol.RestrictableEnumSym, List[Type]), Symbol.EnumSym],
    val instances: Map[(Symbol.TraitSym, TypeConstructor), Instance]
  ) {
    private val specializedDefsQueue: ConcurrentLinkedQueue[(Symbol.DefnSym, MonoAst.Def)] = new ConcurrentLinkedQueue()

    /** Records `defn` under its fresh specialized `sym`. */
    def addSpecializedDef(sym: Symbol.DefnSym, defn: MonoAst.Def): Unit =
      specializedDefsQueue.add((sym, defn))

    /** Returns all specialized defs recorded so far. */
    def specializedDefs: Map[Symbol.DefnSym, MonoAst.Def] =
      specializedDefsQueue.asScala.toMap

    /** Diagnostic only, for MonomorphBench's Xmonobench table. */
    private val defCategoryCountsQueue: ConcurrentLinkedQueue[String] = new ConcurrentLinkedQueue()

    /** Increments the count for `category` (one of "regularDefs"/"instanceDefs"/"defaultSigImpls"). */
    def incrementDefCategory(category: String): Unit =
      defCategoryCountsQueue.add(category)

    /** Returns the per-category specialized-def counts. */
    def defCategoryCounts: Map[String, Int] =
      defCategoryCountsQueue.asScala.groupMapReduce(identity)(_ => 1)(_ + _)
  }

  /**
    * Returns the sym to use for a call to `sym` at ground arrow type `groundArrowTpe`.
    */
  private[monomorph2] def lookupSym(sym: Symbol.DefnSym, groundArrowTpe: Type)
                       (implicit sctx: SharedContext): Symbol.DefnSym = {
    val defn = sctx.allDefs.getOrElse(sym, throw InternalCompilerException(s"lookupSym: sym not in allDefs: $sym", sym.loc))
    // instance/default-sig defs can have empty spec.tparams but still need specialization
    // therefore we first look it up in `sctx.defTable`
    sctx.defTable.get((sym, groundArrowTpe)) match {
      case Some(specializedSym) => specializedSym
      case None =>
        if (defn.spec.tparams.isEmpty) {
          defn.sym
        } else {
          throw InternalCompilerException(
            s"Solver gap: no specialization for $sym at type $groundArrowTpe. " +
              "Extend the constraint generator to cover this call site.", sym.loc)
        }
    }
  }

  /**
    * Returns the case sym to use for a `Tag`/`Pattern.Tag` at ground enum type `groundEnumTpe`.
    */
  private[monomorph2] def lookupCaseSym(caseSym: Symbol.CaseSym, groundEnumTpe: Type)(implicit sctx: SharedContext): Symbol.CaseSym = {
    val argTypes = groundEnumTpe.typeArguments
    sctx.enumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, caseSym.ordinal, caseSym.loc)
      case None  =>
        if (argTypes.isEmpty) {
          caseSym
        } else {
          throw InternalCompilerException(
            s"Solver gap: no enum specialization for ${caseSym.enumSym} at $argTypes. " +
              "Extend the constraint generator to cover this call site.", caseSym.loc)
        }
    }
  }

  /** `RestrictableCaseSym` has no ordinal of its own to carry over when it is rebuilt as a `CaseSym`.
    * But we must use this same value, since ordinal is part of `CaseSym`'s equality.
    */
  private val NoOrdinal: Int = -1

  /**
    * Returns the (regular) case sym for a restrictable tag/pattern at ground restrictable-enum
    * type `groundRestrictableEnumTpe`.
    */
  private[monomorph2] def lookupRestrictableCaseSym(caseSym: Symbol.RestrictableCaseSym, groundRestrictableEnumTpe: Type)(implicit sctx: SharedContext): Symbol.CaseSym = {
    val argTypes = groundRestrictableEnumTpe.typeArguments
    sctx.restrictableEnumTable.get((caseSym.enumSym, argTypes)) match {
      case Some(freshEnumSym) => new Symbol.CaseSym(freshEnumSym, caseSym.name, NoOrdinal, caseSym.loc)
      case None =>
        throw InternalCompilerException(
          s"Solver gap: no restrictable enum specialization for ${caseSym.enumSym} at $argTypes. " +
            "Extend the constraint generator to cover this call site.", caseSym.loc)
    }
  }

  /**
    * Returns the struct sym for a `StructNew`/`StructGet`/`StructPut` at ground type
    * `groundStructTpe`.
    */
  private[monomorph2] def lookupStructSym(sym: Symbol.StructSym, groundStructTpe: Type)(implicit sctx: SharedContext): Symbol.StructSym = {
    val argTypes = groundStructTpe.typeArguments
    sctx.structTable.get((sym, argTypes)) match {
      case Some(freshStructSym) => freshStructSym
      case None =>
        if (argTypes.isEmpty) {
          sym
        } else {
          throw InternalCompilerException(
            s"Solver gap: no struct specialization for $sym at $argTypes. " +
              "Extend the constraint generator to cover this call site.", groundStructTpe.loc)
        }
    }
  }

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
      case Type.Var(sym, _)                         => s.m.get(sym) match {
        case None    => Canonicalization.default(tpe0)
        case Some(t) => t
      }

      case Type.Cst(TypeConstructor.Region(_), loc) => Type.Cst(RegionInstantiation, loc)

      case Type.Cst(_, _)                           => tpe0

      case app@Type.Apply(_, _, _)                  => Canonicalization.normalizeApply(apply, app, isGround = true)

      case Type.Alias(_, _, t, _)                   => apply(t)

      case Type.AssocType(symUse, arg0, kind, loc)  =>
        val arg = apply(arg0)
        val assoc = Type.AssocType(symUse, arg, kind, loc)
        val reducedType = Canonicalization.reduceAssocType(assoc)
        Canonicalization.simplify(reducedType, isGround = true)

      case Type.JvmToType(_, loc)                   => throw InternalCompilerException("unexpected JVM type", loc)
      case Type.JvmToEff(_, loc)                    => throw InternalCompilerException("unexpected JVM eff", loc)
      case Type.UnresolvedJvmType(_, loc)           => throw InternalCompilerException("unexpected JVM type", loc)
    }
  }

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
        // declaredScheme.base needs the same canonicalization as fparams/retTpe/eff because
        // enumTable/structTable lookups are keyed on canonicalized types.
        val canonScheme = declaredScheme.copy(base = StrictSubstitution.empty(declaredScheme.base))
        val spec = TypedAst.Spec(doc, ann, mod, tparams, fparams, canonScheme, StrictSubstitution.empty(retTpe), StrictSubstitution.empty(eff), tconstrs, econstrs)
        TypedAst.Op(sym, spec, loc)
    }

  /** Returns the `def` that implements signature `sym` for the instance at ground arrow type `groundArrowTpe`, or its trait-level default. */
  private[monomorph2] def resolveSigSym(sym: Symbol.SigSym, groundArrowTpe: Type)
                            (implicit sctx: SharedContext, root: TypedAst.Root, flix: Flix): TypedAst.Def = {
    val sig = root.sigs(sym)
    val trt = root.traits(sym.trt)
    val subst = ConstraintSolver2.fullyUnify(sig.spec.declaredScheme.base, groundArrowTpe, RegionScope.Top, RigidityEnv.empty)(root.eqEnv, flix).get
    val traitType = subst.m(trt.tparam.sym)
    val tyCon = traitType.typeConstructor.get
    val instance = sctx.instances((sym.trt, tyCon))
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

  /** Rewrites any specialized `Enum`/`Struct`/`RestrictableEnum` reference in `tpe` to its fresh sym.
    * `tpe` must already be substituted and lowered (i.e. only ever called via `visitType`/
    * `visitTypeSubstituted`).
    */
  private[monomorph2] def rewriteEnumStructType(tpe: Type)(implicit sctx: SharedContext): Type = tpe match {
    case Type.Cst(_, _)                    => tpe

    case Type.Apply(_, _, loc)             =>
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

    case Type.Var(_, loc)                  => throw InternalCompilerException("Unexpected type variable", loc)
    case Type.AssocType(_, _, _, loc)      => throw InternalCompilerException("Unexpected associated type", loc)
    case Type.JvmToType(_, loc)            => throw InternalCompilerException("Unexpected JVM type", loc)
    case Type.JvmToEff(_, loc)             => throw InternalCompilerException("Unexpected JVM eff", loc)
    case Type.UnresolvedJvmType(_, loc)    => throw InternalCompilerException("Unexpected JVM type", loc)
  }

  /** Applies [[rewriteEnumStructType]] to every type embedded in `spec`. */
  private def rewriteSpec(spec: MonoAst.Spec)(implicit sctx: SharedContext): MonoAst.Spec =
    spec.copy(
      fparams = spec.fparams.map(rewriteFormalParam),
      functionType = rewriteEnumStructType(spec.functionType),
      retTpe = rewriteEnumStructType(spec.retTpe),
      eff = rewriteEnumStructType(spec.eff)
    )

  /** Applies [[rewriteEnumStructType]] to `fp`'s type. */
  private[monomorph2] def rewriteFormalParam(fp: MonoAst.FormalParam)(implicit sctx: SharedContext): MonoAst.FormalParam =
    fp.copy(tpe = rewriteEnumStructType(fp.tpe))

  /**
    * Applies [[rewriteEnumStructType]] to every op's `Spec` in `eff` — op specs skip
    * [[SpecializeAndLower.visitType]]'s inline rewrite entirely, so this is the only pass they get.
    */
  private def rewriteEffect(eff: MonoAst.Effect)(implicit sctx: SharedContext): MonoAst.Effect =
    eff.copy(ops = eff.ops.map(op => op.copy(spec = rewriteSpec(op.spec))))

  /**
    * Returns every def reachable from `root` — top-level, instance, and default-sig-impl — plus
    * the tables [[mkDefEntries]] needs for each one's declared type parameters.
    */
  private def mkAllDefs(root: TypedAst.Root): (Map[Symbol.DefnSym, TypedAst.Def], Map[Symbol.DefnSym, TypedAst.Instance], Map[Symbol.DefnSym, TypedAst.Def], Map[Symbol.DefnSym, List[TypedAst.TypeParam]]) = {
    // Instance defs live in root.instances, not root.defs.
    val allInstanceDefs: Map[Symbol.DefnSym, TypedAst.Def] =
      root.instances.values.flatMap(_.defs).map(d => d.sym -> d).toMap
    // Instance-def sym → its owning Instance (for inst.tparams lookup).
    val defToInst: Map[Symbol.DefnSym, TypedAst.Instance] =
      root.instances.values.flatMap(inst => inst.defs.map(d => d.sym -> inst)).toMap
    // Default sig impls don't exist as TypedAst.Def — sig.exp is the trait-level body; synthesize
    // one using the same sym formula as ConstraintGen.
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

    (root.defs ++ allInstanceDefs ++ defaultSigDefs, defToInst, defaultSigDefs, defaultSigTraitTparams)
  }

  /**
    * Returns one `(freshSym, defn, subst, instantiatedType)` entry per `(sym, tuple)` the solver
    * found reachable, for every parametric def. Solver tuples are
    * `[inst.tparams values..., sig-own tparams values...]` for instance/default-sig defs. A tuple
    * that fails to instantiate (e.g. a defaulted `AnyType` needing a nonexistent instance) is
    * silently dropped rather than crashing.
    */
  private def mkDefEntries(
    solution: Solution,
    allDefs: Map[Symbol.DefnSym, TypedAst.Def],
    defToInst: Map[Symbol.DefnSym, TypedAst.Instance],
    defaultSigTraitTparams: Map[Symbol.DefnSym, List[TypedAst.TypeParam]]
  )(implicit root: TypedAst.Root, flix: Flix): List[(Symbol.DefnSym, TypedAst.Def, StrictSubstitution, Type)] =
    for {
      (sym, tuples)  <- solution.defs.toList
      defn           <- allDefs.get(sym).toList
      tuple          <- tuples.map(_.args)
      instTparams     = defToInst.get(sym).map(_.tparams).getOrElse(Nil)
      // Prepended in the solver tuple but not in defn.spec.tparams.
      traitTparams    = defaultSigTraitTparams.getOrElse(sym, Nil)
      // Pairs with the tuple prefix; defn.spec.tparams pairs with the suffix.
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

  /**
    * Returns one `(sym, tuple, freshSym, newEnum)` entry per `(sym, tuple)` the solver found
    * reachable, for every enum with a nonempty tparams list. Same drop-on-failure behavior as
    * [[mkDefEntries]].
    */
  private def mkEnumEntries(solution: Solution)(implicit root: TypedAst.Root, flix: Flix): List[(Symbol.EnumSym, List[Type], Symbol.EnumSym, TypedAst.Enum)] =
    for {
      (sym, tuples) <- solution.enums.toList
      enm           <- root.enums.get(sym).toList
      if enm.tparams.nonEmpty
      tuple         <- tuples.map(_.args)
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

  /**
    * Same as [[mkEnumEntries]], except the tuple is zipped against `index :: tparams` (the
    * case-set index is always the first solved argument), and the result is a plain
    * `TypedAst.Enum` — restrictable enums lower to regular enums.
    */
  private def mkRestrictableEnumEntries(solution: Solution)(implicit root: TypedAst.Root, flix: Flix): List[(Symbol.RestrictableEnumSym, List[Type], Symbol.EnumSym, TypedAst.Enum)] =
    for {
      (sym, tuples) <- solution.restrictableEnums.toList
      enm           <- root.restrictableEnums.get(sym).toList
      tuple         <- tuples.map(_.args)
      substMap       = (enm.index :: enm.tparams).zip(tuple).map { case (tp, ty) => tp.sym -> ty }.toMap
      freshSym       = Symbol.freshEnumSym(SpecializeAndLower.lowerRestrictableEnumSym(sym))
      subst         <- try {
                         List(StrictSubstitution.mk(Substitution(substMap)))
                       } catch {
                         case _: InternalCompilerException => Nil
                       }
    } yield {
      val newCases = enm.cases.map { case (caseSym, TypedAst.RestrictableCase(_, tpes, sc, cloc)) =>
        val newCaseSym = new Symbol.CaseSym(freshSym, caseSym.name, NoOrdinal, caseSym.loc)
        newCaseSym -> TypedAst.Case(newCaseSym, tpes.map(subst.apply), sc, cloc)
      }
      (sym, tuple, freshSym, TypedAst.Enum(enm.doc, enm.ann, enm.mod, freshSym, Nil, enm.derives, newCases, enm.loc))
    }

  /** Same shape as [[mkEnumEntries]], for structs. */
  private def mkStructEntries(solution: Solution)(implicit root: TypedAst.Root, flix: Flix): List[(Symbol.StructSym, List[Type], Symbol.StructSym, TypedAst.Struct)] =
    for {
      (sym, tuples) <- solution.structs.toList
      struct        <- root.structs.get(sym).toList
      if struct.tparams.nonEmpty
      tuple         <- tuples.map(_.args)
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

  /** Specializes `root` per `solution`, the constraint solver's output from Phase 3. */
  def run(root: TypedAst.Root, solution: Solution)(implicit flix: Flix): MonoAst.Root = flix.phase("Monomorpher") {
    implicit val r: TypedAst.Root = root
    val is: Map[(Symbol.TraitSym, TypeConstructor), Instance] = MonomorphHelpers.mkInstanceMap(root.instances)

    val (allDefs, defToInst, defaultSigDefs, defaultSigTraitTparams) = mkAllDefs(root)

    val entries = mkDefEntries(solution, allDefs, defToInst, defaultSigTraitTparams)
    // defTable: (original sym, instantiated arrow type) → fresh specialized sym.
    val defTableMap: Map[(Symbol.DefnSym, Type), Symbol.DefnSym] =
      entries.map { case (freshSym, defn, _, it) => (defn.sym, it) -> freshSym }.toMap

    val enumEntries = mkEnumEntries(solution)
    val enumTableMap: Map[(Symbol.EnumSym, List[Type]), Symbol.EnumSym] =
      enumEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    val restrictableEnumEntries = mkRestrictableEnumEntries(solution)
    val restrictableEnumTableMap: Map[(Symbol.RestrictableEnumSym, List[Type]), Symbol.EnumSym] =
      restrictableEnumEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    val structEntries = mkStructEntries(solution)
    val structTableMap: Map[(Symbol.StructSym, List[Type]), Symbol.StructSym] =
      structEntries.map { case (sym, tuple, freshSym, _) => (sym, tuple) -> freshSym }.toMap

    implicit val sctx: SharedContext = new SharedContext(defTableMap, allDefs, enumTableMap, structTableMap, restrictableEnumTableMap, is)

    // Biggest-first scheduling reduces long-tail stragglers (same convention as
    // Typer/Lexer/Weeder2/Parser2's ParOps.*WithPriority uses).
    def sortBySize(defn: TypedAst.Def): Int = defn.loc.startLine - defn.loc.endLine

    // Non-parametric: no spec.tparams, no instance tparams, and not a default-sig impl.
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

    // Generic originals are dropped: every reachable instantiation already has a specialized copy
    // in enumEntries, reached via the strict lookupCaseSym/lookupStructSym. Restrictable enums
    // have no non-parametric case at all — see specializedRestrictableEnums below.
    val enums = ParOps.parMapValues(root.enums.filter { case (_, e) => e.tparams.isEmpty }) {
      case TypedAst.Enum(doc, ann, mod, sym, tparams, derives, cases, loc) =>
        SpecializeAndLower.lowerEnum(TypedAst.Enum(doc, ann, mod, sym, tparams, derives, MapOps.mapValues(cases)(visitEnumCase), loc))
    }

    // One specialized declaration per (sym, tuple) the solver found reachable.
    val specializedEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(enumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SpecializeAndLower.lowerEnum(newEnum) }.toMap

    // Same as specializedEnums, for restrictableEnumEntries.
    val specializedRestrictableEnums: Map[Symbol.EnumSym, MonoAst.Enum] =
      ParOps.parMap(restrictableEnumEntries) { case (_, _, freshSym, newEnum) => freshSym -> SpecializeAndLower.lowerEnum(newEnum) }.toMap

    val structs = ParOps.parMapValues(root.structs.filter { case (_, s) => s.tparams.isEmpty }) {
      case TypedAst.Struct(doc, ann, mod, sym, tparams, sc, fields, loc) =>
        SpecializeAndLower.lowerStruct(TypedAst.Struct(doc, ann, mod, sym, tparams, sc, MapOps.mapValues(fields)(visitStructField), loc))
    }

    val specializedStructs: Map[Symbol.StructSym, MonoAst.Struct] =
      ParOps.parMap(structEntries) { case (_, _, freshSym, newStruct) => freshSym -> SpecializeAndLower.lowerStruct(newStruct) }.toMap

    // Diagnostic only — MonomorphBench must treat this as pipeline-specific data.
    flix.emitEvent(FlixEvent.AfterMonomorphCategories(sctx.defCategoryCounts))

    MonoAst.Root(
      sctx.specializedDefs,
      enums ++ specializedEnums ++ specializedRestrictableEnums,
      structs ++ specializedStructs,
      effects,
      root.mainEntryPoint,
      root.entryPoints,
      root.sources
    )
  }
}
