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

import ca.uwaterloo.flix.language.ast.TypedAst.Expr
import ca.uwaterloo.flix.language.ast.ops.TypedAstOps
import ca.uwaterloo.flix.language.ast.{Symbol, Type, TypeConstructor, TypedAst}
import ca.uwaterloo.flix.util.collection.ListMap

/**
  * Generic helpers shared across the constraint-based monomorphization pipeline. Unlike
  * [[MonomorphCanon]], nothing here carries a "solver and specializer must agree" contract —
  * these are plain, reusable tree-walking utilities.
  */
private[monomorph2] object MonomorphHelpers {

  /**
    * Returns `true` if the given variable symbol `sym` is a quantified variable according to the
    * given constraint params `cparams0`.
    *
    * That is, the variable symbol is *NOT* lexically bound.
    */
  def isQuantifiedVar(sym: Symbol.VarSym, cparams0: List[TypedAst.ConstraintParam]): Boolean =
    cparams0.exists(p => p.bnd.sym == sym)

  /** Returns the free variables of `exp0` that are bound by the constraint params `cparams0`. */
  def quantifiedVars(cparams0: List[TypedAst.ConstraintParam], exp0: Expr): List[(Symbol.VarSym, Type)] =
    TypedAstOps.freeVars(exp0).toList.filter { case (sym, _) => isQuantifiedVar(sym, cparams0) }

  // Copied from monomorph.Specialization.mkInstanceMap; keep in sync if that baseline changes.
  /** Creates a table for fast lookup of instances. */
  def mkInstanceMap(instances: ListMap[Symbol.TraitSym, TypedAst.Instance]): Map[(Symbol.TraitSym, TypeConstructor), TypedAst.Instance] =
    instances.map { case (sym, inst) => ((sym, inst.tpe.typeConstructor.get), inst) }.toMap
}
