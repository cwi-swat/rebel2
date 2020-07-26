module rebel::checker::tests::ExpectationRunnerTester

import rebel::checker::ExpectationRunner;
import rebel::lang::Syntax;

import util::PathUtil;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import rebel::checker::Trace;

import IO;
import util::Benchmark;

void checkAllExpectations(loc modul, int solverTimeout = 0) {
  println("Checking all expectation in module");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  int startTime = realTime();
  list[ExpectationResult] results = checkExpectations(m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout);
  int endTime = realTime();
  
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
  
  println("Total time of checking expectations: <(endTime - startTime)>ms.");
}

void checkExpectation(str check, loc modul, int solverTimeout = 0) {
 println("Checking expectation `<check>` in module");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  int startTime = realTime();
  ExpectationResult result = checkExpectation(findCheck(m, check), m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout);
  int endTime = realTime();
  
  println();
  println("===========================");
  
  switch (result) {
    case asExpected(str c): println("Check `<c>` as expected");
    case notAsExpected(str c, str reason, Trace t): {
      println("Check `<c>` NOT as expected: <reason>");
      println(trace2Str(t));
    }
  }
  
  println("Total time of checking expectation: <(endTime - startTime)>ms.");
}

private Check findCheck(Module m, str check) = chk
  when /chk:(Check)`<Command _> <Id name> from <Id _> in <SearchDepth _> <Objectives? _> <Expect expect>;` := m.parts, 
       "<name>" == check;