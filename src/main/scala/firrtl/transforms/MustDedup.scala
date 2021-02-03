// See LICENSE for license details.

package firrtl.transforms

import firrtl._
import firrtl.annotations._
import firrtl.annotations.TargetToken.OfModule
import firrtl.analyses.InstanceKeyGraph
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.options.Dependency
import firrtl.stage.Forms

import java.io.{File, FileWriter}

case class MustDeduplicateAnnotation(modules: Seq[IsModule]) extends MultiTargetAnnotation {
  def targets: Seq[Seq[IsModule]] = modules.map(Seq(_))

  def duplicate(n: Seq[Seq[Target]]): MustDeduplicateAnnotation = {
    val newModules = n.map {
      case Seq(mod: IsModule) => mod
      case other => ???
    }
    MustDeduplicateAnnotation(newModules)
  }
}

/** Specifies the directory where errors for modules that "must deduplicate" will be reported */
case class MustDeduplicateReportDirectory(directory: String) extends NoTargetAnnotation

object MustDeduplicateTransform {
  sealed trait DedupFailureCandidate {
    def message: String
  }
  case class LikelyShouldMatch(a: OfModule, b: OfModule) extends DedupFailureCandidate {
    def message: String = s"Modules '${a.value}' and '${b.value}' likely should dedup but do not!"
  }
  case class DisjointChildren(a: OfModule, b: OfModule) extends DedupFailureCandidate {
    def message: String = s"Modules '${a.value}' and '${b.value}' have disjoint child instances!"
  }

  /** Reports deduplication failures two Modules
    *
    * @return (Set of Modules that only appear in one hierarchy or the other, candidate pairs of Module names)
    */
  def findDedupFailures(shouldDedup: (OfModule, OfModule), graph: InstanceKeyGraph): (Set[OfModule], Seq[DedupFailureCandidate]) = {
    val instLookup = graph.getChildInstances.toMap
    def recurse(a: OfModule, b: OfModule): Seq[DedupFailureCandidate] = {
      val as = instLookup(a.value)
      val bs = instLookup(b.value)
      if (as.length != bs.length) Seq(DisjointChildren(a, b))
      else {
        val fromChildren = as.zip(bs).flatMap {
          case (ax, bx) => recurse(ax.OfModule, bx.OfModule)
        }
        if (fromChildren.nonEmpty) fromChildren else Seq(LikelyShouldMatch(a, b))
      }
    }
    val (a, b) = shouldDedup
    val allMismatches = {
      val digraph = graph.graph.transformNodes(_.OfModule)
      val fromA = digraph.reachableFrom(a).toSet + a
      val fromB = digraph.reachableFrom(b).toSet + b
      (fromA union fromB) diff (fromA intersect fromB)
    }
    val candidates = recurse(a, b)
    (allMismatches, candidates)
  }

  private case class DedupFailure(shouldDedup: Seq[String], relevantMods: Set[OfModule], candidates: Seq[DedupFailureCandidate])
}

// Must run after ExpandWhens
// Requires
//   - static single connections of ground types
class MustDeduplicateTransform extends Transform with DependencyAPIMigration {
  import MustDeduplicateTransform._

  override def prerequisites = Seq(Dependency[DedupModules])

  // Make this run as soon after Dedup as possible
  override def optionalPrerequisiteOf = (Forms.MidForm.toSet -- Forms.HighForm).toSeq

  override def invalidates(a: Transform) = false

  def execute(state: CircuitState): CircuitState = {

    lazy val igraph = InstanceKeyGraph(state.circuit)

    // We do pairs here because it's easier ot reason about
    val dedupFailures: Seq[DedupFailure] =
      state.annotations.collect {
        case MustDeduplicateAnnotation(mods) =>
          val moduleNames = mods.map(_.leafModule).distinct
          val pairs = moduleNames.combinations(2).toList // if size == 1, gets Seq()
          val failures = pairs.map { case Seq(a, b) => findDedupFailures((OfModule(a), OfModule(b)), igraph) }
          val relevantMods = failures.flatMap(_._1).toSet
          val candidates = failures.flatMap(_._2)
          DedupFailure(moduleNames, relevantMods, candidates.distinct)
      }
    if (dedupFailures.nonEmpty) {
      // Create and log reports
      val reports = dedupFailures.map { case DedupFailure(shouldDedup, _, candidates) =>
        val msg =
          s"""${shouldDedup.mkString(", ")} are marked as "must deduplicate", but did not deduplicate.
             |Failure candidates:
             |${candidates.map(" - " + _.message).mkString("\n")}
             |""".stripMargin
        logger.error(msg)
        msg
      }

      // Write reports and modules to disk
      val dirName = state.annotations
                         .collectFirst { case MustDeduplicateReportDirectory(dir) => dir}
                         .getOrElse("dedup_failures")
      val dir = new File(dirName)
      logger.error(s"Writing error report(s) to ${dir}...")
      FileUtils.makeDirectory(dir.toString)
      for ((report, idx) <- reports.zipWithIndex) {
        val f = new File(dir, s"report_$idx.rpt")
        logger.error(s"Writing $f...")
        val fw = new FileWriter(f)
        fw.write(report)
        fw.close()
      }

      val modsDir = new File(dir, "modules")
      FileUtils.makeDirectory(modsDir.toString)
      logger.error(s"Writing relevant modules to $modsDir...")
      val relevantModule = dedupFailures.flatMap(_.relevantMods.map(_.value)).toSet
      for (mod <- state.circuit.modules if relevantModule(mod.name)) {
        val fw = new FileWriter(new File(modsDir, s"${mod.name}.fir"))
        fw.write(mod.serialize)
        fw.close()
      }
    }
    state
  }
}
