module rebel::checker::tests::ExpectationBenchmarker

import rebel::checker::ExpectationRunner;
//import rebel::lang::Syntax;

import util::PathUtil;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import rebel::checker::Trace;
import rebel::lang::Syntax;

import IO;
import lang::csv::IO;

import util::MemoCacheClearer;
import util::Benchmark;

alias ExpectationBenchmarkResult = lrel[int iteration, loc modul, str check, str config, bool asExpected, bool solverTimeout, int checkAssemblyDuration, int normDuration, int configBuildDuration, int translateToAlleDuration, int translateToSmtDuration, int solveDurationSolver, int solveDurationTotal, int relModelCreationDuration, int total, int observedTotalDuration, int nrOfSmtVars, int nrOfSmtClauses];

void benchmarkAllExpectations(list[loc] moduls, loc csvOutputFile, int solverTimeout = 0, int warmup = 0, int iterations = 1, set[str] skip = {}) {
  ExpectationBenchmarkResult intermediateResult = [];
    
  for (loc modul <- moduls) {
    intermediateResult = benchmarkExpectations(modul, csvOutputFile, intermediateResult = intermediateResult, solverTimeout = solverTimeout, warmup = warmup, iterations = iterations, skip = skip);
  }  
}

ExpectationBenchmarkResult benchmarkExpectations(loc modul, loc csvOutputFile, ExpectationBenchmarkResult intermediateResult = [], int solverTimeout = 0, int warmup = 0, int iterations = 1, set[str] skip = {}) {
  println("Benchmarking all expectation in module `<modul>` with a warmup of <warmup> and # iterations <iterations>");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  ExpectationResult singleRun(Check chk) {
    clearMemoCache(alleAlleMods());
    gc();
  
    return checkExpectation(chk, m, tr.tm, depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout, countNrOfVars = true, countNrOfClauses = true);
  }
  
  ExpectationBenchmarkResult outcome = intermediateResult;
  
  for (/chk:(Check)`<Command _> <Id name> from <Id _> in <SearchDepth _> <Objectives? _> <Expect _>;` := m.parts, "<name>" notin skip) {
    println("Warming up to benchmark expectation <name>, running #<warmup> rounds");
    for (int _ <- [0..warmup]) {
      singleRun(chk);
    }
    println("Warmup done");

    println("Starting benchmark runs for expectation <name>, running #<iterations>, rounds");      
    list[ExpectationResult] results = [];
    for (int i <- [0..iterations]) {
      println("Start iteration <i+1> of <iterations>");
      results += singleRun(chk);
    }
    println("End of benchmarking runs for expectation <name>, saving results to csv");
  
    outcome = (outcome | it + consOutcome(modul, i, results[i]) | int i <- [0..iterations]);
    writeCSV(outcome, csvOutputFile);
  }
  
  return outcome;
}

private ExpectationBenchmarkResult consOutcome(loc modul, int iteration, ExpectationResult res) =
  [<iteration, modul, res.check, res.config, asExpected(_,_) := res, solverTimedout(_,_) := res, res.checkAssemblyDuration, res.normDuration, res.configBuildDuration, res.translateToAlleDuration, res.translateToSmtDuration, res.solveDurationSolver, res.solveDurationTotal, res.relModelCreationDuration, calcTotal(res), res.observedTotalDuration, res.nrOfSmtVars, res.nrOfSmtClauses>]; 
  
private int calcTotal(ExpectationResult res) = res.checkAssemblyDuration + res.normDuration + res.configBuildDuration + res.translateToAlleDuration + res.translateToSmtDuration + res.solveDurationSolver + res.solveDurationTotal + res.relModelCreationDuration;