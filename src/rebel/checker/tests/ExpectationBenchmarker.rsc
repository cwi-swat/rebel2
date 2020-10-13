module rebel::checker::tests::ExpectationBenchmarker

import rebel::checker::ExpectationRunner;
//import rebel::lang::Syntax;

import util::PathUtil;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import rebel::checker::Trace;

import IO;
import lang::csv::IO;
import DateTime;

alias ExpectationBenchmarkResult = lrel[datetime timestamp, loc modul, str check, str config, bool asExpected, bool solverTimeout, int checkAssemblyDuration, int normDuration, int configBuildDuration, int translateToAlleDuration, int translateToSmtDuration, int solveDurationSolver, int solveDurationTotal, int relModelCreationDuration, int total, int observedTotalDuration];

void benchmarkAllExpectations(list[loc] moduls, loc csvOutputFile, int solverTimeout = 0) {
  ExpectationBenchmarkResult intermediateResult = [];
    
  for (loc modul <- moduls) {
    intermediateResult = benchmarkExpectations(modul, csvOutputFile, intermediateResult = intermediateResult, solverTimeout = solverTimeout);
  }  
}

ExpectationBenchmarkResult benchmarkExpectations(loc modul, loc csvOutputFile, ExpectationBenchmarkResult intermediateResult = [], int solverTimeout = 0) {
  println("Checking all expectation in module `<modul>`");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  list[ExpectationResult] results = checkExpectations(m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout);
  
  ExpectationBenchmarkResult outcome = (intermediateResult | it + consOutcome(modul, res) | res <- results);
  
  writeCSV(outcome, csvOutputFile);
  
  return outcome;
}

private ExpectationBenchmarkResult consOutcome(loc modul, ExpectationResult res) =
  [<now(), modul, res.check, res.config, asExpected(_,_) := res, solverTimedout(_,_) := res, res.checkAssemblyDuration, res.normDuration, res.configBuildDuration, res.translateToAlleDuration, res.translateToSmtDuration, res.solveDurationSolver, res.solveDurationTotal, res.relModelCreationDuration, calcTotal(res), res.observedTotalDuration>]; 
  
private int calcTotal(ExpectationResult res) = res.checkAssemblyDuration + res.normDuration + res.configBuildDuration + res.translateToAlleDuration + res.translateToSmtDuration + res.solveDurationSolver + res.solveDurationTotal + res.relModelCreationDuration;