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
import ca.uwaterloo.flix.language.ast.{MonoAst, TypedAst}
import ca.uwaterloo.flix.language.dbg.AstPrinter

/**
  * Entry point for the constraint-based monomorphization pipeline: generates flow constraints,
  * rejects non-monomorphizable programs, solves the constraints, then specializes accordingly.
  */
object ConstraintMonomorphization {

  /**
    * Monomorphizes `root` via constraint generation, solving, and specialization.
    */
  def run(root: TypedAst.Root)(implicit flix: Flix): MonoAst.Root = {
    val constraints = ConstraintCollection.generate(root)
    flix.phase("NonMonomorphizableCheck") {
      NonMonomorphizableCheck.checkMonomorphizable(constraints)
    }(AstPrinter.DebugNoOp())
    val solution = ConstraintSolver.solve(constraints, root)
    SolutionSpecialization.run(root, solution)
  }
}
