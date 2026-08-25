/*
 * Copyright 2026 Flix Authors
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
package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.{CompilerConstants, Flix}
import ca.uwaterloo.flix.language.ast.shared.SecurityContext
import ca.uwaterloo.flix.util.{InternalCompilerException, Options}
import org.scalatest.BeforeAndAfterAll
import org.scalatest.funsuite.AnyFunSuite

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters.*

/**
  * `NonMonomorphizableCheck` throws a raw [[InternalCompilerException]] instead of reporting a
  * normal `CompilationMessage`, so these tests can't use `TestUtils.check`/`expectError` the way
  * every other `TestX` in this package does.
  * Reaching it also requires the full backend pipeline (it runs inside
  * [[ca.uwaterloo.flix.api.Flix.codeGen]], behind the `--Xnewmono` flag, using the `ForkJoinPool`
  * `codeGen` itself initializes — `TreeShaker1`/`ConstraintGen` can't safely be invoked piecemeal
  * from outside it). So each test type-checks the input, then calls `codeGen` directly, and
  * asserts whether the run throws.
  */
class TestMonomorph2 extends AnyFunSuite with BeforeAndAfterAll {

  private implicit val sctx: SecurityContext = SecurityContext.Unrestricted

  private var preExistingCrashReports: Set[Path] = Set.empty

  override def beforeAll(): Unit = {
    preExistingCrashReports = listCrashReports()
  }

  override def afterAll(): Unit = {
    // Every expected InternalCompilerException below goes through CrashHandler.handleCrash on
    // its way out, which writes a crash_report_N.txt to the working directory — clean up
    // whatever this suite added, but leave alone anything that was already there.
    for (p <- listCrashReports() -- preExistingCrashReports) {
      Files.deleteIfExists(p)
    }
  }

  private def listCrashReports(): Set[Path] = {
    val cwd = Paths.get(".")
    Files.list(cwd).iterator().asScala.filter(p => p.getFileName.toString.matches("crash_report_\\d+\\.txt")).toSet
  }

  /** Type-checks `input`, then runs it through `codeGen` (with `--Xnewmono` on). */
  private def checkMonomorphizable(input: String, o: Options = Options.TestWithLibMin.copy(xnewmono = true)): Unit = {
    val flix = new Flix().setOptions(o)
    flix.addVirtualPath(CompilerConstants.VirtualTestFile, input)
    val (root, errors) = flix.check()
    if (errors.nonEmpty) {
      fail(s"Expected the input to type-check, but got: ${errors.mkString(", ")}")
    }
    flix.codeGen(root.get)
    ()
  }

  // =========================================================================
  // Polymorphic recursion — functions
  // =========================================================================

  test("PolymorphicRecursion.Function.01") {
    // Growing via tupling. Return type is Int32, not `a`: `a -> a` would need `a = (a, a)`.
    val input =
      """
        |def loop(x: a): Int32 = loop((x, x))
        |def main(): Unit \ IO = println(loop(1))
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  test("PolymorphicRecursion.Function.02") {
    // Growing via an enum wrapper instead of a tuple.
    val input =
      """
        |enum Box[a] { case B(a) }
        |def loop(x: a): Int32 = loop(Box.B(x))
        |def main(): Unit \ IO = println(loop(1))
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  test("PolymorphicRecursion.Function.Unreachable.01") {
    // Reached only via `unused`, which nothing calls — TreeShaker1 removes it first.
    val input =
      """
        |def loop(x: a): Int32 = loop((x, x))
        |def unused(): Int32 = loop(1)
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    checkMonomorphizable(input) // must not throw
  }

  // =========================================================================
  // Polymorphic recursion — cycles spanning multiple definitions
  // =========================================================================

  test("PolymorphicRecursion.Function.Cycle.GrowingMiddle.01") {
    // f -> g -> h -> f. The growing edge (g calling h) sits in the middle of the cycle,
    // not on the def where the cycle is first detected.
    val input =
      """
        |def f(x: a): Int32 = g(x)
        |def g(y: b): Int32 = h((y, y))
        |def h(z: c): Int32 = f(z)
        |def main(): Unit \ IO = println(f(1))
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  test("PolymorphicRecursion.Function.Cycle.GrowingClosing.01") {
    // p -> q -> r -> p. The growing edge is the one that closes the cycle back to p.
    val input =
      """
        |def p(x: a): Int32 = q(x)
        |def q(y: b): Int32 = r(y)
        |def r(z: c): Int32 = p((z, z))
        |def main(): Unit \ IO = println(p(1))
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  // =========================================================================
  // Polymorphic recursion — enums
  // =========================================================================

  test("PolymorphicRecursion.Enum.MutualCycle.01") {
    // Even and Odd recurse into each other rather than directly into themselves — the growing
    // edge (Even embedding Odd[(a, a)]) is one hop away from the enum where it's flagged.
    val input =
      """
        |enum Even[a] { case EZero, case ESucc(Odd[(a, a)]) }
        |enum Odd[a]  { case OSucc(Even[a]) }
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  test("PolymorphicRecursion.Enum.01") {
    // Growing case is actually constructed.
    val input =
      """
        |enum PerfectTree[a] {
        |    case Leaf(a)
        |    case Node(PerfectTree[(a, a)])
        |}
        |def size(t: PerfectTree[b]): Int32 = match t {
        |    case PerfectTree.Leaf(_)     => 1
        |    case PerfectTree.Node(inner) => 2 * size(inner)
        |}
        |def main(): Unit \ IO = {
        |    let t = PerfectTree.Node(PerfectTree.Leaf((1, 2)));
        |    println(size(t))
        |}
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  test("PolymorphicRecursion.Enum.Unconstructed.01") {
    // Unlike defs, TreeShaker1 does not filter unused enum/struct declarations.
    val input =
      """
        |enum NonRegular[a] {
        |    case Simple(a)
        |    case Recurse(NonRegular[(a, a)])
        |}
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  // =========================================================================
  // Polymorphic recursion — structs
  // =========================================================================

  test("PolymorphicRecursion.Struct.01") {
    // Struct mirror of Enum.Unconstructed.01 — same reasoning applies to structs.
    val input =
      """
        |struct NonRegular[a, r] {
        |    simple: a,
        |    recurse: NonRegular[(a, a), r]
        |}
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  // =========================================================================
  // Polymorphic recursion — restrictable enums
  // =========================================================================

  test("PolymorphicRecursion.RestrictableEnum.01") {
    // Restrictable-enum mirror of Enum.Unconstructed.01 — the case-set index `s` stays fixed,
    // only the regular type param `a` grows.
    val input =
      """
        |restrictable enum NonRegular[s][a] {
        |    case Simple(a)
        |    case Recurse(NonRegular[s][(a, a)])
        |}
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    assertThrows[InternalCompilerException] {
      checkMonomorphizable(input)
    }
  }

  // =========================================================================
  // Sanity: ordinary (non-growing) recursion must not be rejected
  // =========================================================================

  test("OrdinaryRecursion.Function.01") {
    val input =
      """
        |enum MyList[a] { case MyNil, case MyCons(a, MyList[a]) }
        |def sum(l: MyList[Int32]): Int32 = match l {
        |    case MyList.MyNil         => 0
        |    case MyList.MyCons(x, xs) => x + sum(xs)
        |}
        |def main(): Unit \ IO = println(sum(MyList.MyCons(1, MyList.MyNil)))
      """.stripMargin
    checkMonomorphizable(input) // must not throw
  }

  test("OrdinaryRecursion.Enum.01") {
    val input =
      """
        |enum MyList[a] { case MyNil, case MyCons(a, MyList[a]) }
        |def main(): Unit \ IO = println("ok")
      """.stripMargin
    checkMonomorphizable(input) // must not throw
  }
}
