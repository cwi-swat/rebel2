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
import lang::csv::IO;

void checkAllExpectations(loc modul, int solverTimeout = 0) {
  println("Checking all expectation in module");
  
  m = parseModule(modul);

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  
  int startTime = cpuTime();
  list[ExpectationResult] results = checkExpectations(m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout);
  int endTime = cpuTime();
  
  println();
  println("===========================");
  
  for (r <- results) {
    switch (r) {
      case asExpected(str c, str _): println("Check `<c>` as expected. <durations2str(r)>");
      case notAsExpected(str c, str _, str reason, Trace t): {
        println("Check `<c>` NOT as expected: <reason>. <durations2str(r)>");
        println(trace2Str(t));
      }
    }
  }
  
  println("Total time of checking all expectations: <(endTime - startTime) / 1000000> ms.");
}

void checkExpectation(str check, loc modul, int solverTimeout = 0) {
  println("Checking expectation `<check>` in module");
  
  m = parseModule(modul);

  int startTime = cpuTime();

  PathConfig pcfg = defaultPathConfig(modul);
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug = false);
  ExpectationResult result = checkExpectation(findCheck(m, check), m, tr.tm, tr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = solverTimeout);

  int endTime = cpuTime();
  
  println();
  println("===========================");
  
  switch (result) {
    case r:asExpected(str c, _): println("Check `<c>` as expected. <durations2str(r)>");
    case r:notAsExpected(str c, str _, str reason, Trace t): {
      println("Check `<c>` NOT as expected: <reason>. <durations2str(r)>");
      println(trace2Str(t));
    }
  }
  
  println("Total time of checking expectation: <(endTime - startTime)/1000000> ms.");
}

private Check findCheck(Module m, str check) = chk
  when /chk:(Check)`<Command _> <Id name> from <Id _> in <SearchDepth _> <Objectives? _> <Expect _>;` := m.parts, 
       "<name>" == check;