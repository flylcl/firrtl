// See LICENSE for license details.

package firrtl.transforms

import firrtl._
import firrtl.annotations._
import firrtl.annotations.TargetToken.OfModule
import firrtl.analyses.InstanceKeyGraph
import firrtl.analyses.InstanceKeyGraph.InstanceKey
import firrtl.options.Dependency
import firrtl.stage.Forms
import firrtl.graph.DiGraph

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
    def modules: Seq[OfModule]
  }
  case class LikelyShouldMatch(a: OfModule, b: OfModule) extends DedupFailureCandidate {
    def message: String = s"Modules '${a.value}' and '${b.value}' likely should dedup but do not!"
    def modules = Seq(a, b)
  }
  case class DisjointChildren(a: OfModule, b: OfModule) extends DedupFailureCandidate {
    def message: String = s"Modules '${a.value}' and '${b.value}' have disjoint child instances!"
    def modules = Seq(a, b)
  }

  final class DeduplicationFailureException(msg: String) extends FirrtlUserException(msg)

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

  // TODO move these to object or class DiGraph
  private def prettifyDiGraph(graph: DiGraph[String]): String = prettifyDiGraph[String](graph)(x => x)
  private def prettifyDiGraph[A](graph: DiGraph[A])(f: A => String): String = {
    val (l, n, c) = {
      val cs = options.DependencyManagerUtils.PrettyCharSet
      (cs.lastNode, cs.notLastNode, cs.continuation)
    }
    val ctab = " " * c.size + " "
    def rec(tab: String, node: A, mark: String, prev: List[String]): List[String] = {
      val here = s"$mark${f(node)}"
      val children = graph.getEdges(node)
      val last = children.size - 1
      children.toList // From LinkedHashSet to List to avoid determinism issues
              .zipWithIndex // Find last
              .foldLeft(here :: prev) {
          case (acc, (nodex, idx)) =>
            val nextTab = if (idx == last) tab + ctab else tab + c + " "
            val nextMark = if (idx == last) tab + l else tab + n
            rec(nextTab, nodex, nextMark + " ", acc)
       }
    }
    graph.findSources
         .foldLeft(Nil: List[String]) {
      case (acc, root) => rec("", root, "", acc)
    }.reverse.mkString("\n")
  }

  // Creates new DiGraph of only the nodes reachable from the passed arguments
  private def subgraphReachableFrom[A](graph: DiGraph[A], roots: Set[A]): DiGraph[A] = {
    val vprime = roots.flatMap(graph.reachableFrom(_)) ++ roots
    graph.subgraph(vprime)
  }

  private case class DedupFailure(shouldDedup: Seq[String], relevantMods: Set[OfModule], candidates: Seq[DedupFailureCandidate])

  /** Turn a [[DedupFailure]] into a pretty graph for visualization */
  private def makePrettyTreeOfFailure(failure: DedupFailure, graph: DiGraph[String], getParents: String => Seq[String]): String = {
    val DedupFailure(shouldDedup, _, candidates) = failure
    val shouldDedupSet = shouldDedup.toSet
    // Create a graph rooted at the "shouldDedup" nodes
    val mygraph =
      subgraphReachableFrom(graph, shouldDedupSet) +
      // Add fake nodes to represent parents of the "shouldDedup" nodes
      DiGraph(shouldDedup.map(n => getParents(n).mkString(", ") -> n): _*)
    // Gather candidate modules and assign indices for reference
    val candidateIdx: Map[String, Int] =
      candidates.zipWithIndex
                .flatMap { case (c, idx) => c.modules.map(_.value -> idx) }
                .toMap
    // Now mark the graph for modules of interest
    val markedGraph = mygraph.transformNodes { n =>
      val next = if (shouldDedupSet(n)) s"($n)" else n
      candidateIdx.get(n)
                  .map(i => s"$next [$i]")
                  .getOrElse(next)
    }
    prettifyDiGraph(markedGraph)
  }
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
      val modgraph = igraph.graph.transformNodes(_.module)
      // Lookup the parent Module name of any Module
      val getParents: String => Seq[String] =
        modgraph.reverse
                .getEdgeMap
                .mapValues(_.toSeq)
      // Create and log reports
      val reports = dedupFailures.map { case fail @ DedupFailure(shouldDedup, _, candidates) =>
        val graph = makePrettyTreeOfFailure(fail, modgraph, getParents)
        val msg =
          s"""${shouldDedup.mkString(", ")} are marked as "must deduplicate", but did not deduplicate.
             |$graph
             |Failure candidates:
             |${candidates.zipWithIndex.map { case (c, i) => s" - [$i] " + c.message }.mkString("\n")}
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

      val msg = s"Modules marked 'must deduplicate' failed to deduplicate! See error reports in $dirName"
      throw new DeduplicationFailureException(msg)
    }
    state
  }
}
