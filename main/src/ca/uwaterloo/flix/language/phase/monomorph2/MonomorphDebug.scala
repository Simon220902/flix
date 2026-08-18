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

import ca.uwaterloo.flix.api.{CompilerConstants, Flix}
import ca.uwaterloo.flix.util.FileOps
import ca.uwaterloo.flix.util.tc.Debug

/**
  * `--Xprint-phases` dumps for the constraint-based monomorphization pipeline.
  *
  * Writes to `build/asts/monomorph2/` with real `.dot`/`.txt` extensions (bypassing
  * [[AstPrinter]]'s shared `writeToDisk`, which hardcodes `.flixir`) so the files are directly
  * usable by Graphviz and text editors.
  */
private[monomorph2] object MonomorphDebug {

  /** Writes `flows` as a Graphviz graph and a plain-text listing, both prefixed with stats. */
  object DebugFlows extends Debug[List[FlowConstraint]] {
    override def emit(name: String, flows: List[FlowConstraint])(implicit flix: Flix): Unit = {
      val dir = CompilerConstants.AstDirectory.resolve("monomorph2")
      val statLines = stats(flows)
      FileOps.writeString(dir.resolve("ConstraintCollection.dot"), statLines.map("// " + _).mkString("\n") + "\n\n" + toDot(flows))
      FileOps.writeString(dir.resolve("ConstraintCollection.txt"), statLines.mkString("\n") + "\n\n" + flowsToText(flows))
    }
  }

  /** Writes `solution` as a plain-text listing of every symbol's solved ground tuples. */
  object DebugSolution extends Debug[Solution] {
    override def emit(name: String, solution: Solution)(implicit flix: Flix): Unit = {
      val dir = CompilerConstants.AstDirectory.resolve("monomorph2")
      FileOps.writeString(dir.resolve("ConstraintSolver.txt"), solutionToText(solution))
    }
  }

  /** Returns a short human-readable label for `mvar`, e.g. `Def(map)`. */
  private[monomorph2] def monoVarLabel(mvar: MonoVar): String = mvar match {
    case MonoVar.Def(sym)              => s"Def(${sym.name})"
    case MonoVar.Enum(sym)             => s"Enum(${sym.name})"
    case MonoVar.Sig(sym)              => s"Sig(${sym.name})"
    case MonoVar.RestrictableEnum(sym) => s"REnum(${sym.name})"
    case MonoVar.Struct(sym)           => s"Struct(${sym.text})"
  }

  /**
    * Renders `flows` as a Graphviz DOT string: one node per MonoVar (boxes=defs, ellipses=enums,
    * diamonds=sigs), seed edges from plaintext constant nodes, propagation edges between MonoVars.
    */
  private def toDot(flows: List[FlowConstraint]): String = {
    val sb = new StringBuilder
    sb.append("digraph constraints {\n")
    sb.append("  rankdir=LR;\n")
    sb.append("  node [fontname=\"Courier\", fontsize=10];\n")
    sb.append("  edge [fontname=\"Courier\", fontsize=8];\n\n")

    allMonoVarsOf(flows).foreach {
      mvar =>
        val (shape, color) = mvar match {
          case _: MonoVar.Def              => ("box",     "lightblue")
          case _: MonoVar.Enum             => ("ellipse", "lightyellow")
          case _: MonoVar.Sig              => ("diamond", "lightgreen")
          case _: MonoVar.RestrictableEnum => ("ellipse", "lightsalmon")
          case _: MonoVar.Struct           => ("box",     "lightcyan")
        }
        sb.append(s"""  ${dotId(mvar)} [label="${dotEscape(monoVarLabel(mvar))}", shape=$shape, style=filled, fillcolor=$color];\n""")
    }

    sb.append("\n")

    var seedCount = 0
    flows.foreach { case FlowConstraint(Instantiation(args), dst) =>
      val srcMVars = args.flatMap(collectMonoVars)
      val label = args.map(monoArgLabel).mkString(", ")
      if (srcMVars.isEmpty) {
        val sid = s"seed$seedCount"
        seedCount += 1
        sb.append(s"""  $sid [label="${dotEscape(label)}", shape=plaintext];\n""")
        sb.append(s"""  $sid -> ${dotId(dst)};\n""")
      } else {
        srcMVars.distinct.foreach {
          src =>
            sb.append(s"""  ${dotId(src)} -> ${dotId(dst)} [label="${dotEscape(label)}"];\n""")
        }
      }
    }

    sb.append("}\n")
    sb.toString
  }

  /** Returns every `MonoVar` appearing in `flows`, as either a destination or a source argument. */
  private def allMonoVarsOf(flows: List[FlowConstraint]): List[MonoVar] =
    flows.flatMap { case FlowConstraint(Instantiation(args), dst) => List(dst) ++ args.flatMap(collectMonoVars) }

  /** Returns every `MonoVar` referenced by a `Param` inside `arg`. */
  private def collectMonoVars(arg: MonoArg): List[MonoVar] =
    MonoArg.collectParams(arg).map(_._1)

  /** Returns summary stats for `flows`: total flow/MonoVar counts plus a per-kind breakdown. */
  private def stats(flows: List[FlowConstraint]): List[String] = {
    val allMVars = allMonoVarsOf(flows)
    val byKind = allMVars.groupBy {
      case _: MonoVar.Def              => "Def"
      case _: MonoVar.Enum             => "Enum"
      case _: MonoVar.Sig              => "Sig"
      case _: MonoVar.RestrictableEnum => "RestrictableEnum"
      case _: MonoVar.Struct           => "Struct"
    }.view.mapValues(_.size).toList.sortBy(_._1)
    s"flows: ${flows.size}" :: s"distinct MonoVars: ${allMVars.size}" :: byKind.map { case (k, n) => s"  $k: $n" }
  }

  /** Returns a plain-text listing of `flows`, one line per flow: `<args> -> <destination>`. */
  private def flowsToText(flows: List[FlowConstraint]): String =
    flows.map { case FlowConstraint(Instantiation(args), dst) =>
      s"${args.map(monoArgLabel).mkString(", ")} -> ${monoVarLabel(dst)}"
    }.sorted.mkString("\n")

  /** Returns a plain-text listing of `solution`: summary stats, then every solved tuple by category. */
  private def solutionToText(solution: Solution): String = {
    def section[K](title: String, mk: K => MonoVar, m: Map[K, List[GroundInstantiation]]): String = {
      val lines = m.toList.map { case (k, tuples) =>
        s"${monoVarLabel(mk(k))} -> ${tuples.map(t => s"[${t.args.mkString(", ")}]").sorted.mkString(", ")}"
      }.sorted
      s"$title (${m.size} symbols, ${m.values.map(_.size).sum} tuples):\n" + lines.mkString("\n")
    }

    val header = List(
      s"total symbols: ${solution.defs.size + solution.enums.size + solution.structs.size + solution.restrictableEnums.size}",
      s"total tuples: ${(solution.defs.values ++ solution.enums.values ++ solution.structs.values ++ solution.restrictableEnums.values).map(_.size).sum}"
    ).mkString("\n")

    header + "\n\n" +
      section("Defs", MonoVar.Def(_), solution.defs) + "\n\n" +
      section("Enums", MonoVar.Enum(_), solution.enums) + "\n\n" +
      section("Structs", MonoVar.Struct(_), solution.structs) + "\n\n" +
      section("RestrictableEnums", MonoVar.RestrictableEnum(_), solution.restrictableEnums) + "\n"
  }

  /** Returns a DOT-safe node id for `mvar`. */
  private def dotId(mvar: MonoVar): String = {
    val raw = mvar match {
      case MonoVar.Def(sym)              => s"def_${sanitize(sym.toString)}"
      case MonoVar.Enum(sym)             => s"enum_${sanitize(sym.toString)}"
      case MonoVar.Sig(sym)              => s"sig_${sanitize(sym.toString)}"
      case MonoVar.RestrictableEnum(sym) => s"renum_${sanitize(sym.toString)}"
      case MonoVar.Struct(sym)           => s"struct_${sanitize(sym.toString)}"
    }
    s""""$raw""""
  }

  /** Returns a short human-readable label for `arg`. */
  private def monoArgLabel(arg: MonoArg): String = arg match {
    case MonoArg.Param(v, i)         => s"p(${monoVarLabel(v)},$i)"
    case MonoArg.Const(tpe)          => tpe.toString
    case MonoArg.App(tc, args)       => s"App(${monoArgLabel(tc)},${args.map(monoArgLabel).mkString(",")})"
    case MonoArg.Assoc(sym, a, _, _) => s"Assoc(${sym.name},${monoArgLabel(a)})"
  }

  /** Replaces DOT-unsafe characters with underscores in node ids. */
  private def sanitize(s: String): String =
    s.replaceAll("[^A-Za-z0-9_]", "_")

  /** Escapes double-quotes and backslashes for DOT label strings. */
  private def dotEscape(s: String): String =
    s.replace("\\", "\\\\").replace("\"", "\\\"")

}
