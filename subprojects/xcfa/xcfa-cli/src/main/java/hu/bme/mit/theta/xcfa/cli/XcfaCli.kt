/*
 *  Copyright 2022 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.xcfa.cli

import com.beust.jcommander.JCommander
import com.beust.jcommander.Parameter
import com.beust.jcommander.ParameterException
import com.google.common.base.Stopwatch
import com.google.gson.GsonBuilder
import com.google.gson.JsonParser
import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.SafetyResult
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.utils.ArgVisualizer
import hu.bme.mit.theta.analysis.utils.TraceVisualizer
import hu.bme.mit.theta.c2xcfa.getXcfaFromC
import hu.bme.mit.theta.common.CliUtils
import hu.bme.mit.theta.common.logging.ConsoleLogger
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.common.visualization.*
import hu.bme.mit.theta.common.visualization.writer.GraphvizWriter
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr
import hu.bme.mit.theta.core.type.inttype.IntModExpr
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Dereference
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.BitwiseChecker
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager
import hu.bme.mit.theta.xcfa.analysis.ErrorDetection
import hu.bme.mit.theta.xcfa.analysis.XcfaAction
import hu.bme.mit.theta.xcfa.analysis.XcfaState
import hu.bme.mit.theta.xcfa.cli.utils.XcfaWitnessWriter
import hu.bme.mit.theta.xcfa.cli.witnesses.XcfaTraceConcretizer
import hu.bme.mit.theta.xcfa.getFlatLabels
import hu.bme.mit.theta.xcfa.model.toDot
import hu.bme.mit.theta.xcfa.passes.LbePass
import java.awt.Color
import java.io.File
import java.io.FileInputStream
import java.io.FileReader
import java.util.*
import java.util.concurrent.TimeUnit
import javax.script.Bindings
import javax.script.ScriptEngine
import javax.script.ScriptEngineManager
import javax.script.SimpleBindings
import kotlin.system.exitProcess


interface ConstraintRule {
    val p: String
    val q: String
}

class ReferencingConstraintRule(override val p: String, override val q: String) : ConstraintRule
class DereferencingWriteConstraintRule(override val p: String, override val q: String) : ConstraintRule
class DereferencingReadConstraintRule(override val p: String, override val q: String) : ConstraintRule
class AliasingConstraintRule(override val p: String, override val q: String) : ConstraintRule

class DisjointSet<T> {
    private val parent = mutableMapOf<T, T>()
    private val rank = mutableMapOf<T, Int>()

    fun makeSet(x: T) {
        parent[x] = x
        rank[x] = 0
    }

    fun find(x: T): T {
        if (parent[x] != x) {
            parent[x] = find(parent[x]!!)
        }
        return parent[x]!!
    }

    fun union(x: T, y: T) {
        val xRoot = find(x)
        val yRoot = find(y)

        if (xRoot == yRoot) {
            return
        }

        if (rank[xRoot]!! < rank[yRoot]!!) {
            parent[xRoot] = yRoot
        } else if (rank[xRoot]!! > rank[yRoot]!!) {
            parent[yRoot] = xRoot
        } else {
            parent[yRoot] = xRoot
            rank[xRoot] = rank[xRoot]!! + 1
        }
    }

    fun getSets(): Map<T, List<T>> {
        val sets = mutableMapOf<T, MutableList<T>>()
        for (x in parent.keys) {
            val root = find(x)
            if (sets.containsKey(root)) {
                sets[root]!!.add(x)
            } else {
                sets[root] = mutableListOf(x)
            }
        }
        return sets
    }
}

class XcfaCli(private val args: Array<String>) {
    //////////// CONFIGURATION OPTIONS BEGIN ////////////
    //////////// input task ////////////
    @Parameter(names = ["--input"], description = "Path of the input C program", required = true)
    var input: File? = null

    @Parameter(names = ["--property"], description = "Path of the property file")
    var property: File? = null

    @Parameter(names = ["--lbe"], description = "Level of LBE (NO_LBE, LBE_LOCAL, LBE_SEQ, LBE_FULL)")
    var lbeLevel: LbePass.LBELevel = LbePass.LBELevel.LBE_SEQ

    //////////// backend options ////////////
    @Parameter(names = ["--backend"], description = "Backend analysis to use")
    var backend: Backend = Backend.CEGAR

    @Parameter(names = ["--strategy"], description = "Execution strategy")
    var strategy: Strategy = Strategy.PORTFOLIO

    @Parameter(names = ["--portfolio"], description = "Portfolio type (only valid with --strategy PORTFOLIO)")
    var portfolio: Portfolio = Portfolio.COMPLEX

    @Parameter(names = ["--smt-home"], description = "The path of the solver registry")
    var solverHome: String = SmtLibSolverManager.HOME.toAbsolutePath().toString()

    //////////// debug options ////////////
    @Parameter(names = ["--stacktrace"], description = "Print full stack trace in case of exception")
    var stacktrace: Boolean = false

    @Parameter(names = ["--no-analysis"], description = "Executes the model transformation to XCFA and CFA, and then exits; use with --output-results to get data about the (X)CFA")
    var noAnalysis = false

    @Parameter(names = ["--print-config"], description = "Print the config to a JSON file (takes a filename as argument)")
    var printConfigFile: String? = null


    //////////// output data and statistics ////////////
    @Parameter(names = ["--version"], description = "Display version", help = true)
    var versionInfo = false

    @Parameter(names = ["--loglevel"], description = "Detailedness of logging")
    var logLevel = Logger.Level.MAINSTEP

    @Parameter(names = ["--output-results"], description = "Creates a directory, in which it outputs the xcfa, cex and witness")
    var outputResults = false

    @Parameter(names = ["--output-directory"], description = "Specify the directory where the result files are stored")
    var resultFolder: File = File("results-${Date()}")

    @Parameter(names = ["--witness-only"], description = "Does not output any other files, just a violation/correctness witness only")
    var svcomp = false

    @Parameter(names = ["--cex-solver"], description = "Concretizer solver name")
    var concretizerSolver: String = "Z3"

    @Parameter(names = ["--validate-cex-solver"], description = "Activates a wrapper, which validates the assertions in the solver in each (SAT) check. Filters some solver issues.")
    var validateConcretizerSolver: Boolean = false

    @Parameter
    var remainingFlags: MutableList<String> = ArrayList()

    private fun run() {
        /// Checking flags
        try {
            JCommander.newBuilder().addObject(this).programName(JAR_NAME).build().parse(*args)
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            ex.printStackTrace()
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }
        val explicitProperty: ErrorDetection =
                if(property != null) {
                    remainingFlags.add("--error-detection")
                    if(property!!.name.endsWith("unreach-call.prp")) {
                        remainingFlags.add(ErrorDetection.ERROR_LOCATION.toString())
                        ErrorDetection.ERROR_LOCATION
                    } else if (property!!.name.endsWith("no-data-race.prp")) {
                        remainingFlags.add(ErrorDetection.DATA_RACE.toString())
                        if(lbeLevel != LbePass.LBELevel.NO_LBE) {
                            System.err.println("Changing LBE type to NO_LBE because the DATA_RACE property will be erroneous otherwise")
                            lbeLevel = LbePass.LBELevel.NO_LBE
                        }
                        ErrorDetection.DATA_RACE
                    } else if (property!!.name.endsWith("no-overflow.prp")) {
                        remainingFlags.add(ErrorDetection.OVERFLOW.toString())
                        if(lbeLevel != LbePass.LBELevel.NO_LBE) {
                            System.err.println("Changing LBE type to NO_LBE because the OVERFLOW property will be erroneous otherwise")
                            lbeLevel = LbePass.LBELevel.NO_LBE
                        }
                        ErrorDetection.OVERFLOW
                    } else {
                        remainingFlags.add(ErrorDetection.NO_ERROR.toString())
                        System.err.println("Unknown property $property, using full state space exploration (no refinement)")
                        ErrorDetection.NO_ERROR
                    }
                } else ErrorDetection.ERROR_LOCATION

        /// version
        if (versionInfo) {
            CliUtils.printVersion(System.out)
            return
        }
        val logger = ConsoleLogger(logLevel)

        /// Starting frontend
        val swFrontend = Stopwatch.createStarted()
        LbePass.level = lbeLevel

        val xcfa = try {
            val stream = FileInputStream(input!!)
            val xcfaFromC = getXcfaFromC(stream, explicitProperty == ErrorDetection.OVERFLOW)
            logger.write(Logger.Level.INFO, "Frontend finished: ${xcfaFromC.name}  (in ${swFrontend.elapsed(TimeUnit.MILLISECONDS)} ms)\n")
            logger.write(Logger.Level.RESULT, "Arithmetic: ${BitwiseChecker.getBitwiseOption()}\n")
            xcfaFromC
        } catch (e: Exception) {
            if (stacktrace) e.printStackTrace();
            logger.write(Logger.Level.RESULT, "Frontend failed!\n")
            exitProcess(ExitCodes.FRONTEND_FAILED.code)
        }
        swFrontend.reset().start()

        // Pointer Analysis
        val pointerConstraintRules = mutableListOf<ConstraintRule>()
        val pointerVariables = mutableSetOf<String>()

        // Andersen's Pointer Analysis

        val main = xcfa.initProcedures.first().first
        val edges = main.edges
        edges.forEach { edge ->
            val labels = edge.label.getFlatLabels()
            labels.forEach { label ->
                val stmt = label.toStmt()
                if (stmt is AssignStmt<*>) {
                    val assignStmt = stmt as AssignStmt<*>
                    val expr = assignStmt.expr
                    if (expr is Reference<*, *>) {
                        val target = assignStmt.varDecl.name
                        val refName = expr.op.toString()
                        // println("Referencing: $target = &$refName ($assignStmt)")
                        // mayPointTo.getOrPut(target) { mutableSetOf() }.add(refName)
                        val p = target;
                        val i = refName;
                        // p = &i
                        // i ∈ pts(p)
                        // pointsTo.getOrPut(p) { mutableListOf() }.add(mutableSetOf(i))
                        pointerConstraintRules.add(ReferencingConstraintRule(p, i))
                        pointerVariables.add(p)
                        pointerVariables.add(i)
                    }
                    if (expr is ArrayWriteExpr<*, *> && expr.array is RefExpr<*>) {
                        // println("Dereferencing-write: *${expr.index} = ${expr.elem} ($assignStmt)")
                        val p = expr.index.toString()
                        val q = expr.elem.toString()
                        // *p = q
                        // ∀x ∈ pts(p): pts(q) ⊆ pts(x)
                        pointerConstraintRules.add(DereferencingWriteConstraintRule(p, q))
                        pointerVariables.add(p)
                        pointerVariables.add(q)
                    }
                    if (expr is IntModExpr && expr.leftOp is Dereference<*, *>) {
                        val leftOp = expr.leftOp as Dereference<*, *>
                        val op = leftOp.op as RefExpr<*>
                        val decl = op.decl
                        // println("Dereferencing-read: ${assignStmt.varDecl.name} = *${decl.name}")
                        val p = assignStmt.varDecl.name
                        val q = decl.name
                        // p = *q
                        // ∀x ∈ pts(q): pts(x) ⊆ pts(p)
                        pointerConstraintRules.add(DereferencingReadConstraintRule(p, q))
                        pointerVariables.add(p)
                        pointerVariables.add(q)
                    }
                    if (expr is RefExpr<*>) {
                        // println("Aliasing ${stmt.varDecl.name} = ${expr.decl.name}")
                        val p = stmt.varDecl.name
                        val q = expr.decl.name
                        // p = q
                        // pts(p) ⊆ pts(q)
                        pointerConstraintRules.add(AliasingConstraintRule(p, q))
                        pointerVariables.add(p)
                        pointerVariables.add(q)
                    }
                }
            }
        }

        val andersensPointsTo = HashMap<String, MutableSet<String>>()
        var lastPointsToLengths = andersensPointsTo.map { it.value.size }.toList()

        while (true) {
            pointerConstraintRules.forEach { rule ->
                when (rule) {
                    is ReferencingConstraintRule -> {
                        val p = rule.p
                        val i = rule.q
                        andersensPointsTo.getOrPut(p) { mutableSetOf() }.add(i)
                    }

                    is DereferencingWriteConstraintRule -> {
                        val p = rule.p
                        val q = rule.q
                        val xs = andersensPointsTo.getOrPut(p) { mutableSetOf() }
                        xs.forEach { x ->
                            andersensPointsTo.getOrPut(x) { mutableSetOf() }.addAll(andersensPointsTo.getOrDefault(q, mutableSetOf()))
                        }
                    }

                    is DereferencingReadConstraintRule -> {
                        val p = rule.p
                        val q = rule.q
                        val xs = andersensPointsTo.getOrPut(q) { mutableSetOf() }
                        xs.forEach { x ->
                            andersensPointsTo.getOrPut(p) { mutableSetOf() }.addAll(andersensPointsTo.getOrDefault(x, mutableSetOf()))
                        }
                    }

                    is AliasingConstraintRule -> {
                        val p = rule.p
                        val q = rule.q
                        andersensPointsTo.getOrPut(p) { mutableSetOf() }.addAll(andersensPointsTo.getOrDefault(q, mutableSetOf()))
                    }
                }
            }

            val newPointsToLengths = andersensPointsTo.map { it.value.size }.toList()

            if (lastPointsToLengths == newPointsToLengths) break
            lastPointsToLengths = newPointsToLengths
        }

        andersensPointsTo.forEach { (target, listOfRefs) -> run {
            listOfRefs.remove(target)
        }}

        andersensPointsTo.forEach { (target, listOfRefs) -> run {
            println("$target -> $listOfRefs")
        }}

        val andersenGraph = Graph(input!!.nameWithoutExtension, input!!.name + " - Andersen's Pointer Analysis")
        val attrsBuilder = NodeAttributes.builder().shape(Shape.RECTANGLE)
                .fillColor(Color.WHITE).lineColor(Color.BLACK).alignment(Alignment.LEFT)
        pointerVariables.forEach {
            andersenGraph.addNode("\"" + it + "\"", attrsBuilder.label(it).build())
        }
        val eAttrs = EdgeAttributes.builder().label("").color(Color.BLACK).lineStyle(LineStyle.NORMAL).font("courier").build()
        andersensPointsTo.forEach { (target, listOfRefs) -> run {
            listOfRefs.forEach {
                andersenGraph.addEdge("\"" + target + "\"", "\"" + it + "\"", eAttrs)
            }
        }}
        GraphvizWriter.getInstance().writeFileAutoConvert(andersenGraph, "andersen" + input!!.nameWithoutExtension + ".dot")

        // / Andersens Pointer Analysis

        // Steensgaard's Pointer Analysis

        val steensgaardsDisjointSets = DisjointSet<String>()
        val steengaardsEdges = mutableSetOf<Pair<String, String>>()
        pointerVariables.forEach { steensgaardsDisjointSets.makeSet(it) }

        fun join(x: String, y: String) {
            if (x == y) return
            val xStar = steengaardsEdges.find { it.first == x }?.second
            val yStar = steengaardsEdges.find { it.first == y }?.second
            steensgaardsDisjointSets.union(x, y)
            if (xStar != null && yStar != null) join(xStar, yStar)
        }
        for (i in 1..3) {
            pointerConstraintRules.forEach{ rule ->
                when (rule) {
                    is ReferencingConstraintRule -> {
                        // p = &q
                        val p = rule.p
                        val i = rule.q
                        val pStar = steengaardsEdges.find { it.first == p }?.second
                        steengaardsEdges.add(Pair(p, i))
                        if (pStar != null) {
                            join(pStar, i)
                        }
                    }

                    is DereferencingWriteConstraintRule -> {
                        // *p = q
                        val p = rule.p
                        val q = rule.q
                        val pStar = steengaardsEdges.find { it.first == p }?.second
                        val pStarStar = steengaardsEdges.find { it.first == pStar }?.second
                        val qStar = steengaardsEdges.find { it.first == q }?.second
                        if (pStar != null && pStarStar != null && qStar != null) {
                            join(pStarStar, qStar)
                        }
                    }

                    is DereferencingReadConstraintRule -> {
                        // p = *q
                        val p = rule.p
                        val q = rule.q
                        val pStar = steengaardsEdges.find { it.first == p }?.second
                        val qStar = steengaardsEdges.find { it.first == q }?.second
                        val qStarStar = steengaardsEdges.find { it.first == qStar }?.second
                        if (pStar != null && qStar != null && qStarStar != null) {
                            join(pStar, qStarStar)
                        }
                    }

                    is AliasingConstraintRule -> {
                        // p = q
                        val p = rule.p
                        val q = rule.q
                        val pStar = steengaardsEdges.find { it.first == p }?.second
                        val qStar = steengaardsEdges.find { it.first == q }?.second
                        if (qStar != null) steengaardsEdges.add(Pair(p, qStar))
                        if (pStar != null && qStar != null) {
                            join(pStar, qStar)
                        }
                    }
                }
            }
        }

        val steensgaardsGraph = Graph(input!!.nameWithoutExtension, input!!.name + " - Steensgaard's Pointer Analysis")
        val steensgaardsAttrsBuilder = NodeAttributes.builder().shape(Shape.RECTANGLE)
                .fillColor(Color.WHITE).lineColor(Color.BLACK).alignment(Alignment.LEFT)
        steensgaardsDisjointSets.getSets().forEach { set ->
            val label = set.value.joinToString(", ")
            steensgaardsGraph.addNode("\"" + set.key + "\"", steensgaardsAttrsBuilder.label(label).build())
        }
        val steensgaardsEAttrs = EdgeAttributes.builder().label("").color(Color.BLACK).lineStyle(LineStyle.NORMAL).font("courier").build()

        val uniqueSteensgaardsEdges = steengaardsEdges.map { Pair(steensgaardsDisjointSets.find(it.first), steensgaardsDisjointSets.find(it.second)) }.toSet()

        uniqueSteensgaardsEdges.forEach { (p, q) ->
            steensgaardsGraph.addEdge("\"" + p + "\"", "\"" + q + "\"", steensgaardsEAttrs)
        }

        GraphvizWriter.getInstance().writeFileAutoConvert(steensgaardsGraph, "steensgaard" + input!!.nameWithoutExtension + ".dot")


        // / Steensgaard's Pointer Analysis

        exitProcess(0)

        val gsonForOutput = getGson()

        if (svcomp || outputResults) {
            if (!svcomp) {
                resultFolder.mkdirs()

                logger.write(Logger.Level.INFO, "Writing results to directory ${resultFolder.absolutePath}")

                val xcfaDotFile = File(resultFolder, "xcfa.dot")
                xcfaDotFile.writeText(xcfa.toDot())

                val xcfaJsonFile = File(resultFolder, "xcfa.json")
                val uglyJson = gsonForOutput.toJson(xcfa)
                val create = GsonBuilder().setPrettyPrinting().create()
                xcfaJsonFile.writeText(create.toJson(JsonParser.parseString(uglyJson)))
            }
        }

        if (noAnalysis) {
            logger.write(Logger.Level.RESULT, "ParsingResult Success")
            return
        }
        registerAllSolverManagers(solverHome, logger)

        val safetyResult: SafetyResult<*, *> =
                when (strategy) {
                    Strategy.DIRECT -> {
                        exitOnError { parseConfigFromCli().check(xcfa, logger) }
                    }

                    Strategy.SERVER -> {
                        val safetyResultSupplier = parseConfigFromCli().checkInProcess(xcfa, solverHome, true, input!!.absolutePath, logger)
                        try {
                            safetyResultSupplier()
                        } catch (e: ErrorCodeException) {
                            exitProcess(e.code)
                        }
                    }

                    Strategy.SERVER_DEBUG -> {
                        val safetyResultSupplier = parseConfigFromCli().checkInProcessDebug(xcfa, solverHome, true, input!!.absolutePath, logger)
                        try {
                            safetyResultSupplier()
                        } catch (e: ErrorCodeException) {
                            exitProcess(e.code)
                        }
                    }

                    Strategy.PORTFOLIO -> {
                        var portfolioDescriptor = File(portfolio.name.lowercase() + ".kts")
                        if(!portfolioDescriptor.exists()) {
                            portfolioDescriptor = File(File(XcfaCli::class.java.protectionDomain.codeSource.location.path).parent, portfolio.name.lowercase() + ".kts")
                            if(!portfolioDescriptor.exists()) {
                                logger.write(Logger.Level.RESULT, "Portfolio file not found: ${portfolioDescriptor.absolutePath}\n")
                                exitProcess(ExitCodes.PORTFOLIO_ERROR.code)
                            }
                        }
                        val kotlinEngine: ScriptEngine = ScriptEngineManager().getEngineByExtension("kts")
                        try {
                            val bindings: Bindings = SimpleBindings()
                            bindings["xcfa"] = xcfa
                            bindings["property"] = explicitProperty
                            bindings["cFileName"] = input!!.absolutePath
                            bindings["logger"] = logger
                            bindings["smtHome"] = solverHome
                            bindings["traits"] = VerificationTraits(
                                    multithreaded = ArchitectureConfig.multiThreading,
                                    arithmetic = BitwiseChecker.getBitwiseOption(),
                            )
                            val portfolioResult = kotlinEngine.eval(FileReader(portfolioDescriptor), bindings) as Pair<XcfaCegarConfig, SafetyResult<*, *>>

                            concretizerSolver = portfolioResult.first.refinementSolver
                            validateConcretizerSolver = portfolioResult.first.validateRefinementSolver

                            portfolioResult.second
                        } catch (e: ErrorCodeException) {
                            exitProcess(e.code)
                        } catch (e: Exception) {
                            logger.write(Logger.Level.RESULT, "Portfolio from $portfolioDescriptor could not be executed.")
                            e.printStackTrace()
                            exitProcess(ExitCodes.PORTFOLIO_ERROR.code)
                        }
                    }
                }
        if (svcomp || outputResults) {
            if (!svcomp) {
                resultFolder.mkdirs()

                val argFile = File(resultFolder, "arg-${safetyResult.isSafe}.dot")
                val g: Graph = ArgVisualizer.getDefault().visualize(safetyResult.arg)
                argFile.writeText(GraphvizWriter.getInstance().writeString(g))

                if(safetyResult.isUnsafe) {
                    val concrTrace: Trace<XcfaState<ExplState>, XcfaAction> = XcfaTraceConcretizer.concretize(safetyResult.asUnsafe().trace as Trace<XcfaState<*>, XcfaAction>?, getSolver(concretizerSolver, validateConcretizerSolver))

                    val traceFile = File(resultFolder, "trace.dot")
                    val traceG: Graph = TraceVisualizer.getDefault().visualize(concrTrace)
                    traceFile.writeText(GraphvizWriter.getInstance().writeString(traceG))
                }

            } else {
                XcfaWitnessWriter().writeWitness(safetyResult, input!!, getSolver(concretizerSolver, validateConcretizerSolver))
            }
        }
        logger.write(Logger.Level.RESULT, safetyResult.toString() + "\n")
    }

    private fun parseConfigFromCli(): XcfaCegarConfig {
        val cegarConfig = XcfaCegarConfig()
        try {
            JCommander.newBuilder().addObject(cegarConfig).programName(JAR_NAME).build().parse(*remainingFlags.toTypedArray())
        } catch (ex: ParameterException) {
            println("Invalid parameters, details:")
            ex.printStackTrace()
            ex.usage()
            exitProcess(ExitCodes.INVALID_PARAM.code)
        }
        return cegarConfig
    }

    companion object {
        private const val JAR_NAME = "theta-xcfa-cli.jar"

        @JvmStatic
        fun main(args: Array<String>) {
            val mainApp = XcfaCli(args)
            mainApp.run()
        }
    }
}