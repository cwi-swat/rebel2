module rebel::checker::tests::ExpectationRunnerTester

import rebel::checker::ExpectationRunner;

import util::PathUtil;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import rebel::checker::Trace;

import IO;
import util::Benchmark;

void checkAllExpectations(loc modul) {
  println("Checking all expectation in module");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  int startTime = cpuTime();
  list[ExpectationResult] results = checkExpectations(m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = 0);
  int endTime = cpuTime();
  
  println();
  println("===========================");
  
  for (r <- results) {
    switch (r) {
      case asExpected(str c): println("Check `<c>` as expected");
      case notAsExpected(str c, str reason, Trace t): {
        println("Check `<c>` NOT as expected: <reason>");
        println(trace2Str(t));
      }
    }
  }
  
  println("Total time of checking expectations: <(endTime - startTime)/1000000>ms.");
}