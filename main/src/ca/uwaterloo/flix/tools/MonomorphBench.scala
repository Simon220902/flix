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
package ca.uwaterloo.flix.tools

import ca.uwaterloo.flix.api.{Bootstrap, Flix, FlixEvent, PhaseTime}
import ca.uwaterloo.flix.language.ast.shared.SecurityContext
import ca.uwaterloo.flix.language.phase.unification.EffUnification3
import ca.uwaterloo.flix.tools.compilertop.Profiler
import ca.uwaterloo.flix.util.{Formatter, Options, Result, StatUtils}
import org.json4s.JsonDSL.*
import org.json4s.native.JsonMethods
import org.json4s.{DefaultFormats, JValue, jvalue2extractable, jvalue2monadic}

import java.io.PrintStream
import java.nio.file.{Files, Path}
import scala.util.control.NonFatal

/**
  * Compares the constraint-based monomorphization pipeline (`monomorph2`) against the
  * demand-driven baseline (`monomorph`) on compile time, bytecode size, declaration counts, and
  * a crude memory measurement — see `flix_monomorphization_internship/notes/benchmarking_plan.md`.
  *
  * Corpus for this first pass is the standard library alone (the same corpus Part C's own
  * 184-vs-165-declaration numbers used) — NOT the wider `main/test/flix/` suite. That was tried
  * first (mirroring `CompilerSuite.scala`'s `mkTestDirCollected`/bundle-everything-into-one-
  * compile pattern) and doesn't work: many test files there are only ever compiled individually
  * in the real suite (`CompilerSuite.scala` actually uses per-file `mkTestDir`, not the bundled
  * variant) and collide on duplicate names when bundled together (e.g. `Test.Dec.Mod.flix` and
  * `Test.Use.Def.flix` both declare a top-level `f`). Per-file iteration over the whole suite is
  * explicit future work (see this tool's own TODO below), not done in this first pass. The
  * community-build corpus is separately still future work too.
  *
  * Which pipeline runs is controlled the same way as everywhere else in the compiler:
  * `--Xnewmono` selects the constraint-based pipeline, its absence selects the baseline (see
  * `Flix.scala`'s `codeGen`, gated on `options.xnewmono`). Since that's baked into the `Options`
  * this whole process was launched with (not something safely flippable mid-JVM), one invocation
  * measures ONE pipeline — same shape as `CompilerPerf`'s own `Xperf`, which also doesn't compare
  * two builds in a single run. Run this command twice (once with `--Xnewmono`, once without), then
  * `Xmonobench --compare` to see the diff.
  *
  * The peak-memory number is deliberately crude (same "sleep + GC + `Runtime.totalMemory -
  * freeMemory`" snapshot `CompilerMemory.scala` already uses) — a real profiler is out of scope
  * for this first pass.
  */
object MonomorphBench {

  /** Where result JSON files are written/read, relative to the output path. */
  private val ResultsDir = "monobench"

  /** The default number of compilations to average over — single runs swing too much (confirmed
    * empirically: the same benchmark gave +75%/+3% total-time deltas back-to-back). */
  private val DefaultN: Int = 5

  /** The default number of discarded compiles before the measured runs, to let the JVM's JIT
    * warm up the classes this pass touches — same "compile once, then measure" shape
    * `CompilerPerf.perfBaseLineWithParInc` already uses (there, for incrementalism; here, purely
    * to burn in the JIT before the timed loop starts). */
  private val DefaultWarmup: Int = 2

  private case class Metrics(
    pipeline: String,
    totalTimeMs: Long,
    codeSizeBytes: Int,
    defCount: Int,
    enumCount: Int,
    structCount: Int,
    monomorphPhaseTimeMs: Long,
    crudeMemoryMb: Long,
    // Def sub-category breakdown — only ever populated for the constraint-based pipeline (via
    // FlixEvent.AfterMonomorphCategories); the demand-driven baseline has no equivalent, so these
    // stay None on a "baseline" Metrics. See Specialize.scala's Context doc comment.
    regularDefs: Option[Int] = None,
    instanceDefs: Option[Int] = None,
    defaultSigImpls: Option[Int] = None,
    // 95% CI half-widths (normal approximation, see ci95Margin) for the three metrics aggregated
    // via median across runs — 0.0 for a single-run Metrics (before aggregate() fills these in).
    totalTimeCi95: Double = 0.0,
    monomorphPhaseTimeCi95: Double = 0.0,
    crudeMemoryCi95: Double = 0.0,
    // Real HotSpot-native allocation (ThreadMXBean.getThreadAllocatedBytes, via the same
    // `Profiler` the `--top` TUI uses headlessly — see `runOnce`), summed across every def whose
    // work landed in the "Monomorpher" phase. NOT the same thing as crudeMemoryMb: this is total
    // bytes *allocated* (includes anything since garbage-collected), not a point-in-time heap
    // snapshot — a churn/pressure signal, not a working-set size. Scope is also narrower than the
    // whole monomorph super-phase: only Specialize/Specialization (both already
    // instrumented with flix.profile calls) are covered — ConstraintCollection/ConstraintSolver
    // have no such instrumentation at all, so this says nothing about the new pipeline's
    // suspected-heaviest part (materializing the whole flow-constraint graph up front). Confirmed
    // by grepping every `flix.profile(` call site in both monomorph/ and monomorph2/ before
    // relying on this number — don't assume broader coverage than that.
    specializationAllocMb: Long = 0L,
    specializationAllocCi95: Double = 0.0,
    // Per-phase breakdown of monomorphPhaseTimeMs, keyed by the same phase names used in
    // flix.phaseTimers (e.g. "ConstraintCollection", "ConstraintSolver", "Monomorpher" for the
    // new pipeline; "TreeShaker1", "Monomorpher" for baseline — the two pipelines have different
    // phase sets, "Monomorpher" is the one name they share, see runOnce). No CI per key (unlike
    // the summed total) — this is an informational breakdown of an already-CI-verified number,
    // not an independently significance-tested claim, same precedent as the regularDefs/
    // instanceDefs/defaultSigImpls sub-rows.
    subPhaseTimesMs: Map[String, Long] = Map.empty,
    // Per-phase breakdown of real HotSpot allocation (see specializationAllocMb's doc comment for
    // the mechanism), keyed the same way as subPhaseTimesMs. Only ever non-zero for phases that
    // wrap per-def work in `flix.profile(sym, loc)` — as of writing that's ConstraintCollection
    // (fromDefs/fromInstances/fromSigs) and Monomorpher; ConstraintSolver's fixpoint loop has no
    // per-def shape and is expected to show 0 here (see Avenue 0 in
    // plan_optimization_opportunities.md) until/unless it gets its own instrumentation.
    subPhaseAllocMb: Map[String, Long] = Map.empty,
    // Eraser/Reducer phase times — genuinely separate from subPhaseTimesMs, not folded into it:
    // subPhaseTimesMs's own doc comment defines it as "per-phase breakdown of
    // monomorphPhaseTimeMs", and Eraser/Reducer are backend lowering, not monomorphization. Exists
    // to answer whether the new pipeline's larger upstream declaration count (it specializes more
    // enums/structs than baseline before Eraser/Reducer collapse them, see
    // enum_struct_bytecode_dedup.md) costs extra pre-collapse erasure work even though output
    // class count stays small.
    backendSubPhaseTimesMs: Map[String, Long] = Map.empty
  )

  def run(o: Options, cwd: Path): Unit = {
    if (o.XMonoBenchCompare) {
      compare(o)
    } else {
      val n = o.XPerfN.getOrElse(DefaultN)
      val warmup = o.XMonoBenchWarmup.getOrElse(DefaultWarmup)
      val project = loadProjectIfPresent(cwd, o)

      // Project mode reuses ONE Flix object across every iteration (see `RunContext`'s doc
      // comment for why); stdlib mode keeps the original "fresh Flix() per iteration" pattern
      // (matches CompilerPerf's own convention), since it has no such staleness tracking to fight.
      val sharedCtx = project.map(_ => new RunContext(o))

      (0 until warmup).foreach(_ => runOnce(o, project, sharedCtx))
      val passed = (0 until n).map(_ => runOnce(o, project, sharedCtx)).flatten
      println(s"passed: ${passed.length}/$n")
      if (passed.isEmpty) {
        println("All runs failed to compile — see output above.")
        return
      }

      val metrics = aggregate(passed)
      writeResult(metrics, o)
      printSummary(metrics, passed)
    }
  }

  /** If `cwd` has a `flix.toml`, resolves the project (dependencies + local source files) once
    * via `Bootstrap` — the exact mechanism `flix build` itself uses (see `Main.scala`'s
    * `Command.Build` case) — so the measured loop below pays only real compile cost, not repeated
    * dependency resolution on every iteration. Returns `None` for the original stdlib-only
    * virtual corpus (still the default when this tool is invoked from the flix repo itself, which
    * has no `flix.toml` at its root). */
  private def loadProjectIfPresent(cwd: Path, o: Options): Option[Bootstrap] = {
    if (!Files.exists(cwd.resolve("flix.toml"))) return None

    implicit val formatter: Formatter = Formatter.getDefault
    implicit val out: PrintStream = System.out
    Bootstrap.bootstrap(cwd, o.githubToken) match {
      case Result.Ok(bootstrap) => Some(bootstrap)
      case Result.Err(e) =>
        println(s"Failed to bootstrap project at $cwd: ${e.message(formatter)}")
        System.exit(1)
        None
    }
  }

  /** Runs `runs.length` compiles of the stdlib and combines the noisy metrics (time, memory) via
    * their median — same combine strategy `CompilerPerf.run` uses via `StatUtils.median`. The
    * deterministic metrics (code size, declaration counts) are identical across runs, so the
    * first run's values are kept as-is rather than needlessly re-aggregated. */
  private def aggregate(runs: Seq[Metrics]): Metrics = {
    val head = runs.head
    val subPhaseKeys = runs.flatMap(_.subPhaseTimesMs.keys).distinct
    val subPhaseTimesMs = subPhaseKeys.map { k =>
      k -> StatUtils.median(runs.flatMap(_.subPhaseTimesMs.get(k))).round
    }.toMap
    val subPhaseAllocKeys = runs.flatMap(_.subPhaseAllocMb.keys).distinct
    val subPhaseAllocMb = subPhaseAllocKeys.map { k =>
      k -> StatUtils.median(runs.flatMap(_.subPhaseAllocMb.get(k))).round
    }.toMap
    val backendSubPhaseKeys = runs.flatMap(_.backendSubPhaseTimesMs.keys).distinct
    val backendSubPhaseTimesMs = backendSubPhaseKeys.map { k =>
      k -> StatUtils.median(runs.flatMap(_.backendSubPhaseTimesMs.get(k))).round
    }.toMap
    head.copy(
      totalTimeMs = StatUtils.median(runs.map(_.totalTimeMs)).round,
      monomorphPhaseTimeMs = StatUtils.median(runs.map(_.monomorphPhaseTimeMs)).round,
      crudeMemoryMb = StatUtils.median(runs.map(_.crudeMemoryMb)).round,
      specializationAllocMb = StatUtils.median(runs.map(_.specializationAllocMb)).round,
      totalTimeCi95 = ci95Margin(runs.map(_.totalTimeMs)),
      monomorphPhaseTimeCi95 = ci95Margin(runs.map(_.monomorphPhaseTimeMs)),
      crudeMemoryCi95 = ci95Margin(runs.map(_.crudeMemoryMb)),
      specializationAllocCi95 = ci95Margin(runs.map(_.specializationAllocMb)),
      subPhaseTimesMs = subPhaseTimesMs,
      subPhaseAllocMb = subPhaseAllocMb,
      backendSubPhaseTimesMs = backendSubPhaseTimesMs
    )
  }

  /** Holds one `Flix` object plus the mutable slots its `FlixEvent` listener writes into.
    * `Flix.clearCaches()` (called internally by `Bootstrap.build`) resets AST/type caches and
    * forces `ChangeSet.Everything` but leaves registered listeners alone (confirmed by reading
    * `Flix.scala`) — so reusing one `RunContext` across repeated `bootstrap.build(flix)` calls
    * still gets a genuine full recompile each time, it just avoids re-registering a listener.
    *
    * Project mode MUST reuse one `RunContext`/`Flix` across all iterations, not construct a
    * fresh one per call: `Bootstrap`'s own staleness tracking (`updateStaleSourcesByTimestamp`)
    * only calls `flix.addFile` for a source path the *first* time it sees that path change — a
    * second call against a brand-new, empty `Flix()` sees nothing "stale" (the file's mtime
    * hasn't changed since the first call) and silently adds none of the project's own sources,
    * so every iteration after the first would compile only stdlib. Caught by testing (real
    * decl-count/code-size numbers exactly matching the stdlib-only corpus was the tell — not
    * something reasoning about `Bootstrap`'s API in isolation would have surfaced). */
  private class RunContext(o: Options) {
    val flix = new Flix()
    flix.setOptions(o.copy(progress = false))

    var declCounts: (Int, Int, Int) = (0, 0, 0)
    var categoryCounts: Map[String, Int] = Map.empty
    flix.addListener {
      case FlixEvent.AfterMonomorph(root) =>
        declCounts = (root.defs.size, root.enums.size, root.structs.size)
      case FlixEvent.AfterMonomorphCategories(counts) =>
        categoryCounts = counts
      case _ => ()
    }
  }

  /** Runs one compile (stdlib-only, or `project`'s sources if given) and collects the metrics.
    * `None` means this run failed to compile — a `Result.Err` from `Bootstrap.build`, or (since
    * the constraint-based pipeline throws rather than returning a `Result` on an internal gap,
    * e.g. `Solver gap`/`NonMonomorphizableProgramException`) an uncaught exception. Either way
    * this is exactly axis 4 (crash-vs-no-crash) from `benchmarking_plan.md` — a real project
    * failing here is a genuine finding, not a bug in this tool, so it must not abort the whole
    * measured loop.
    *
    * `sharedCtx` is `Some` for project mode (see `RunContext`'s doc comment for why it must be
    * reused) and `None` for the stdlib-only corpus, which constructs a fresh context every call —
    * the original "fresh Flix() per iteration" pattern, unaffected by any of the above. */
  private def runOnce(o: Options, project: Option[Bootstrap], sharedCtx: Option[RunContext]): Option[Metrics] = {
    // Clear caches between runs — same reasoning as CompilerPerf.runSingle: a warm cache from a
    // prior iteration would skew this iteration's timing.
    EffUnification3.Algebra.Cache.clearCaches()

    val pipeline = if (o.xnewmono) "new" else "baseline"
    val ctx = sharedCtx.getOrElse(new RunContext(o))
    // Reset before this run so a crash (which skips the listener firing) can't report stale
    // counts left over from a previous successful run on a reused context.
    ctx.declCounts = (0, 0, 0)
    ctx.categoryCounts = Map.empty

    // A fresh Profiler every call, even when ctx.flix is being reused across iterations
    // (project mode) — Profiler's own counters accumulate forever with no reset, so a shared
    // instance would report cumulative allocation across every prior iteration by the Nth run,
    // not this run's own number. Installing it directly via setProfiler (not going through
    // Options.compilerTop) means this never launches the interactive `--top` TUI.
    val profiler = new Profiler(() => ctx.flix.getCurrentPhaseName)
    ctx.flix.setProfiler(Some(profiler))

    val compiled =
      try {
        project match {
          case Some(bootstrap) =>
            bootstrap.build(ctx.flix) match {
              case Result.Ok(result) => Some(result)
              case Result.Err(e) =>
                println(s"  [FAIL] ${e.message(Formatter.getDefault)}")
                None
            }
          case None =>
            addInputs(ctx.flix)
            Some(ctx.flix.compile().unsafeGet)
        }
      } catch {
        case NonFatal(e) =>
          println(s"  [CRASH] ${e.getClass.getSimpleName}: ${e.getMessage}")
          None
      }

    compiled.map { result =>
      val phases = ctx.flix.phaseTimers.map { case PhaseTime(phase, time) => phase -> time }
      // NonMonomorphizableCheck: promoted to its own top-level flix.phase(...) in Flix.scala
      // (previously ran nested inside ConstraintSolver.solve, folded into that phase's own
      // timing) — belongs in the monomorph-phase total same as its former host did.
      val monomorphPhases = Set("ConstraintCollection", "ConstraintSolver", "NonMonomorphizableCheck", "TreeShaker1", "Monomorpher")
      val monomorphSubPhaseNs = phases.collect { case (phase, time) if monomorphPhases.contains(phase) => phase -> time }
      val monomorphTimeNs = monomorphSubPhaseNs.map(_._2).sum
      val subPhaseTimesMs = monomorphSubPhaseNs.map { case (phase, time) => phase -> time / 1_000_000 }.toMap

      // Eraser/Reducer: backend lowering, not monomorphization — deliberately kept out of
      // monomorphPhases/subPhaseTimesMs (see Metrics' doc comment on backendSubPhaseTimesMs).
      val backendPhases = Set("Eraser", "Reducer")
      val backendSubPhaseTimesMs = phases.collect { case (phase, time) if backendPhases.contains(phase) => phase -> time / 1_000_000 }.toMap

      // See Metrics' doc comment on specializationAllocMb for what this does and doesn't cover.
      val snapshot = profiler.snapshot()
      val specializationAllocBytes = snapshot.map(_.byPhaseAlloc.getOrElse("Monomorpher", 0L)).sum
      // Generalized per-phase alloc breakdown (see subPhaseAllocMb's doc comment) — only phases
      // that ran AND wrap per-def work in flix.profile show up non-zero here.
      val subPhaseAllocMb = monomorphSubPhaseNs.map { case (phase, _) =>
        phase -> snapshot.map(_.byPhaseAlloc.getOrElse(phase, 0L)).sum / (1_024 * 1_024)
      }.toMap

      sleepAndGc()
      val usedMemory = Runtime.getRuntime.totalMemory() - Runtime.getRuntime.freeMemory()

      val (defCount, enumCount, structCount) = ctx.declCounts
      Metrics(
        pipeline = pipeline,
        totalTimeMs = result.totalTime / 1_000_000,
        codeSizeBytes = result.codeSize,
        defCount = defCount,
        enumCount = enumCount,
        structCount = structCount,
        monomorphPhaseTimeMs = monomorphTimeNs / 1_000_000,
        crudeMemoryMb = usedMemory / (1_024 * 1_024),
        regularDefs = ctx.categoryCounts.get("regularDefs"),
        instanceDefs = ctx.categoryCounts.get("instanceDefs"),
        defaultSigImpls = ctx.categoryCounts.get("defaultSigImpls"),
        specializationAllocMb = specializationAllocBytes / (1_024 * 1_024),
        subPhaseTimesMs = subPhaseTimesMs,
        subPhaseAllocMb = subPhaseAllocMb,
        backendSubPhaseTimesMs = backendSubPhaseTimesMs
      )
    }
  }

  /** Sleeps a bit and hints the GC to run — mirrors `CompilerMemory.scala`. */
  private def sleepAndGc(): Unit = {
    for (_ <- 0 until 5) {
      Thread.sleep(1_000)
      System.gc()
    }
  }

  // TODO: extend to iterate main/test/flix/*.flix per-file (matching CompilerSuite.scala's own
  // mkTestDir) once this first pass's stdlib-only numbers are in — see the class doc comment.

  /** Adds the whole stdlib (via `LibLevel.All`) and nothing else — see the class doc comment. */
  private def addInputs(flix: Flix): Unit = {
    implicit val sctx: SecurityContext = SecurityContext.Unrestricted
    flix.addVirtualPath(Path.of("Empty.flix"), "")
  }

  private def resultsDir(o: Options): Path = o.outputPath.resolve(ResultsDir)

  private def resultFile(o: Options, pipeline: String): Path =
    resultsDir(o).resolve(s"$pipeline.json")

  private def writeResult(m: Metrics, o: Options): Unit = {
    val dir = resultsDir(o)
    Files.createDirectories(dir)
    val json =
      ("pipeline" -> m.pipeline) ~
        ("totalTimeMs" -> m.totalTimeMs) ~
        ("codeSizeBytes" -> m.codeSizeBytes) ~
        ("defCount" -> m.defCount) ~
        ("enumCount" -> m.enumCount) ~
        ("structCount" -> m.structCount) ~
        ("monomorphPhaseTimeMs" -> m.monomorphPhaseTimeMs) ~
        ("crudeMemoryMb" -> m.crudeMemoryMb) ~
        ("regularDefs" -> m.regularDefs) ~
        ("instanceDefs" -> m.instanceDefs) ~
        ("defaultSigImpls" -> m.defaultSigImpls) ~
        ("totalTimeCi95" -> m.totalTimeCi95) ~
        ("monomorphPhaseTimeCi95" -> m.monomorphPhaseTimeCi95) ~
        ("crudeMemoryCi95" -> m.crudeMemoryCi95) ~
        ("specializationAllocMb" -> m.specializationAllocMb) ~
        ("specializationAllocCi95" -> m.specializationAllocCi95) ~
        ("subPhaseTimesMs" -> m.subPhaseTimesMs) ~
        ("subPhaseAllocMb" -> m.subPhaseAllocMb) ~
        ("backendSubPhaseTimesMs" -> m.backendSubPhaseTimesMs)
    Files.writeString(resultFile(o, m.pipeline), JsonMethods.pretty(JsonMethods.render(json)))
  }

  /** Half-width of a 95% CI via the normal approximation (z=1.96).
    * ponytail: normal approx, not a t-distribution — slightly narrow at this sample size (n~5).
    * Upgrade to a t critical value if this ever needs to be exact rather than indicative. */
  private def ci95Margin(xs: Seq[Long]): Double = 1.96 * StatUtils.stdDev(xs) / Math.sqrt(xs.length)

  private def printSummary(m: Metrics, runs: Seq[Metrics]): Unit = {
    val times = runs.map(_.totalTimeMs)
    val monoTimes = runs.map(_.monomorphPhaseTimeMs)
    val timeCi = ci95Margin(times)
    val monoCi = ci95Margin(monoTimes)
    println(s"pipeline:              ${m.pipeline}")
    println(s"total compile time:    ${m.totalTimeMs} ms  (median of ${runs.length} runs, range ${times.min}-${times.max} ms, mean ${StatUtils.average(times).round}±${timeCi.round} ms 95% CI)")
    println(s"monomorph phase time:  ${m.monomorphPhaseTimeMs} ms  (range ${monoTimes.min}-${monoTimes.max} ms, mean ${StatUtils.average(monoTimes).round}±${monoCi.round} ms 95% CI)")
    m.subPhaseTimesMs.toSeq.sortBy(-_._2).foreach { case (phase, ms) => println(f"  $phase%-21s $ms ms") }
    if (m.backendSubPhaseTimesMs.nonEmpty) {
      println("backend phases (not counted in monomorph phase time above):")
      m.backendSubPhaseTimesMs.toSeq.sortBy(-_._2).foreach { case (phase, ms) => println(f"  $phase%-21s $ms ms") }
    }
    println(s"code size:             ${m.codeSizeBytes} bytes")
    println(s"defs:                  ${m.defCount}")
    m.regularDefs.foreach(n => println(s"  regular functions:   $n"))
    m.instanceDefs.foreach(n => println(s"  instance defs:       $n"))
    m.defaultSigImpls.foreach(n => println(s"  default sig impls:   $n"))
    println(s"enums:                 ${m.enumCount}")
    println(s"structs:               ${m.structCount}")
    println(s"memory (crude):        ${m.crudeMemoryMb} MB")
    println(s"specialization alloc:  ${m.specializationAllocMb} MB  (real HotSpot allocation via --top's Profiler)")
    // "Monomorpher" excluded: identical to specializationAllocMb above, already printed.
    val otherSubPhaseAllocMb = m.subPhaseAllocMb - "Monomorpher"
    if (otherSubPhaseAllocMb.values.exists(_ > 0)) {
      println("sub-phase alloc (real, HotSpot; 0 = not per-def-instrumented):")
      otherSubPhaseAllocMb.toSeq.sortBy(-_._2).foreach { case (phase, mb) => println(f"  $phase%-21s $mb MB") }
    }
    println(s"wrote ${ResultsDir}/${m.pipeline}.json")
  }

  /** Reads `baseline.json`/`new.json` (if both exist) and prints a comparison table. */
  private def compare(o: Options): Unit = {
    val baselineFile = resultFile(o, "baseline")
    val newFile = resultFile(o, "new")
    if (!Files.exists(baselineFile) || !Files.exists(newFile)) {
      println(s"Missing results — run Xmonobench once without --Xnewmono and once with it first.")
      println(s"Expected: $baselineFile and $newFile")
      return
    }

    val baseline = readMetrics(baselineFile)
    val newer = readMetrics(newFile)

    // ciOverlap: whether the two 95% CIs (normal approx, see ci95Margin) overlap at all — if they
    // don't, the delta is a real, significant finding at this sample size; if they do, it isn't
    // (see benchmarking_plan.md's "read the significance verdict, not the specific percentage").
    def row(label: String, base: Long, neu: Long, unit: String, baseCi: Option[Double] = None, neuCi: Option[Double] = None): String = {
      val delta = if (base == 0) 0.0 else 100.0 * (neu - base).toDouble / base.toDouble
      // Locale.ROOT: an f-interpolated "%f" is locale-sensitive (e.g. "75,1" on a
      // comma-decimal locale) — force "." so the output is stable across machines.
      val deltaStr = String.format(java.util.Locale.ROOT, "%+6.1f%%", Double.box(delta))
      val ciStr = (baseCi, neuCi) match {
        case (Some(b), Some(n)) =>
          val overlap = Math.abs(neu - base) <= (b + n)
          val sig = if (overlap) "n.s." else "sig."
          f"±$b%-5.0f/ ±$n%-5.0f $sig"
        case _ => "n/a"
      }
      f"| $label%-22s | $base%12d $unit%-3s | $neu%12d $unit%-3s | $deltaStr | $ciStr%18s |"
    }

    // No baseline equivalent exists for these (see Metrics' doc comment) — the value belongs
    // under the "new" column, so the baseline column is left blank, not the other way round.
    // Column widths matched to row()'s "| label(22) | base(12)+unit(3) | new(12)+unit(3) | ... |".
    def subRow(label: String, value: Option[Int]): String =
      f"|   $label%-20s |                     | ${value.map(_.toString).getOrElse("n/a")}%16s |          |                    |"

    // Per-subphase breakdown of "monomorph phase time" — the two pipelines have different phase
    // sets (baseline: TreeShaker1/Monomorpher; new: TreeShaker1/ConstraintCollection/
    // ConstraintSolver/Monomorpher — see Metrics' doc comment on subPhaseTimesMs), so this prints
    // whichever side actually has each phase name, blank on the other side rather than assuming
    // a 1:1 correspondence. No CI/significance column — see subPhaseTimesMs' own doc comment.
    def timeSubRow(label: String, base: Option[Long], neu: Option[Long], unit: String = "ms"): String = {
      val baseStr = base.map(v => f"$v%d $unit").getOrElse("")
      val neuStr = neu.map(v => f"$v%d $unit").getOrElse("")
      f"|   $label%-20s | $baseStr%19s | $neuStr%19s |          |                    |"
    }

    println("| metric                 |      baseline      |        new         |   delta  |    95% CI (±base/±new)    |")
    println("|------------------------|---------------------|---------------------|----------|----------------------------|")
    println(row("total compile time", baseline.totalTimeMs, newer.totalTimeMs, "ms", Some(baseline.totalTimeCi95), Some(newer.totalTimeCi95)))
    println(row("monomorph phase time", baseline.monomorphPhaseTimeMs, newer.monomorphPhaseTimeMs, "ms", Some(baseline.monomorphPhaseTimeCi95), Some(newer.monomorphPhaseTimeCi95)))
    // Sorted by whichever side's time is larger, descending, so the costliest sub-phase leads.
    (baseline.subPhaseTimesMs.keySet ++ newer.subPhaseTimesMs.keySet).toSeq
      .sortBy(k => -Math.max(baseline.subPhaseTimesMs.getOrElse(k, 0L), newer.subPhaseTimesMs.getOrElse(k, 0L)))
      .foreach(k => println(timeSubRow(k, baseline.subPhaseTimesMs.get(k), newer.subPhaseTimesMs.get(k))))
    // Backend (Eraser/Reducer) phases — deliberately excluded from "monomorph phase time" above,
    // see Metrics' doc comment on backendSubPhaseTimesMs.
    (baseline.backendSubPhaseTimesMs.keySet ++ newer.backendSubPhaseTimesMs.keySet).toSeq
      .sortBy(k => -Math.max(baseline.backendSubPhaseTimesMs.getOrElse(k, 0L), newer.backendSubPhaseTimesMs.getOrElse(k, 0L)))
      .foreach(k => println(timeSubRow(k, baseline.backendSubPhaseTimesMs.get(k), newer.backendSubPhaseTimesMs.get(k))))
    println(row("code size", baseline.codeSizeBytes.toLong, newer.codeSizeBytes.toLong, "B"))
    println(row("defs", baseline.defCount.toLong, newer.defCount.toLong, ""))
    println(subRow("regular functions", newer.regularDefs))
    println(subRow("instance defs", newer.instanceDefs))
    println(subRow("default sig impls", newer.defaultSigImpls))
    println(row("enums", baseline.enumCount.toLong, newer.enumCount.toLong, ""))
    println(row("structs", baseline.structCount.toLong, newer.structCount.toLong, ""))
    println(row("memory (crude)", baseline.crudeMemoryMb, newer.crudeMemoryMb, "MB", Some(baseline.crudeMemoryCi95), Some(newer.crudeMemoryCi95)))
    // Real HotSpot allocation via --top's Profiler, Monomorpher phase ONLY — see Metrics' doc
    // comment on specializationAllocMb before reading this as full-pipeline memory coverage.
    println(row("specialization alloc", baseline.specializationAllocMb, newer.specializationAllocMb, "MB", Some(baseline.specializationAllocCi95), Some(newer.specializationAllocCi95)))
    // Per-phase alloc breakdown — same "whichever side has it" shape as timeSubRow, and same
    // "0 means not per-def-instrumented, not necessarily free" caveat as subPhaseAllocMb itself.
    // "Monomorpher" excluded: identical to specializationAllocMb above, already printed.
    ((baseline.subPhaseAllocMb.keySet ++ newer.subPhaseAllocMb.keySet) - "Monomorpher").toSeq
      .sortBy(k => -Math.max(baseline.subPhaseAllocMb.getOrElse(k, 0L), newer.subPhaseAllocMb.getOrElse(k, 0L)))
      .foreach(k => println(timeSubRow(s"$k (alloc)", baseline.subPhaseAllocMb.get(k), newer.subPhaseAllocMb.get(k), unit = "MB")))
  }

  private def readMetrics(p: Path): Metrics = {
    implicit val formats: DefaultFormats.type = DefaultFormats
    val json: JValue = JsonMethods.parse(Files.readString(p))
    Metrics(
      pipeline = (json \ "pipeline").extract[String],
      totalTimeMs = (json \ "totalTimeMs").extract[Long],
      codeSizeBytes = (json \ "codeSizeBytes").extract[Int],
      defCount = (json \ "defCount").extract[Int],
      enumCount = (json \ "enumCount").extract[Int],
      structCount = (json \ "structCount").extract[Int],
      monomorphPhaseTimeMs = (json \ "monomorphPhaseTimeMs").extract[Long],
      crudeMemoryMb = (json \ "crudeMemoryMb").extract[Long],
      regularDefs = (json \ "regularDefs").extractOpt[Int],
      instanceDefs = (json \ "instanceDefs").extractOpt[Int],
      defaultSigImpls = (json \ "defaultSigImpls").extractOpt[Int],
      // extractOpt + getOrElse: old result JSONs (written before this field existed) just read
      // as "no CI data" rather than throwing a MappingException on the missing key.
      totalTimeCi95 = (json \ "totalTimeCi95").extractOpt[Double].getOrElse(0.0),
      monomorphPhaseTimeCi95 = (json \ "monomorphPhaseTimeCi95").extractOpt[Double].getOrElse(0.0),
      crudeMemoryCi95 = (json \ "crudeMemoryCi95").extractOpt[Double].getOrElse(0.0),
      specializationAllocMb = (json \ "specializationAllocMb").extractOpt[Long].getOrElse(0L),
      specializationAllocCi95 = (json \ "specializationAllocCi95").extractOpt[Double].getOrElse(0.0),
      subPhaseTimesMs = (json \ "subPhaseTimesMs").extractOpt[Map[String, Long]].getOrElse(Map.empty),
      subPhaseAllocMb = (json \ "subPhaseAllocMb").extractOpt[Map[String, Long]].getOrElse(Map.empty),
      backendSubPhaseTimesMs = (json \ "backendSubPhaseTimesMs").extractOpt[Map[String, Long]].getOrElse(Map.empty)
    )
  }

}
