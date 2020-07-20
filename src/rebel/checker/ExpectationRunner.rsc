module rebel::checker::ExpectationRunner

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::Trace;

import rebel::checker::ModelChecker;

import util::PathUtil;

import ParseTree;
import IO;

data ExpectationResult
  = asExpected(str check)
  | notAsExpected(str check, str message, Trace trace)
  ;

list[ExpectationResult] checkExpectations(Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true, int solverTimeout = 30 * 1000) 
  = [checkExpectation(chk,m,tm,deps,pcfg=pcfg,saveIntermediateFiles=saveIntermediateFiles, solverTimeout=solverTimeout) | 
      /chk:(Check)`<Command _> <Id name> from <Id _> in <SearchDepth _> <Objectives? _> <Expect expect>;` := m.parts];

ExpectationResult checkExpectation(Check chk, Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true, int solverTimeout = 30 * 1000) {
  if (/Expect expect := chk) {
    println();
    println("Start checking expectation for `<chk.name>`");
    println("=============================");
    
    Trace foundTrace = performCheck(chk,m,tm,deps,pcfg=pcfg,saveIntermediateFiles = saveIntermediateFiles, solverTimeout = solverTimeout);
    
    if (/(ExpectResult)`no trace` := expect) {
      switch (foundTrace) {
        case noTrace(noSolutionFound()): return asExpected("<chk.name>");
        case t:noTrace(solverTimeout()): return notAsExpected("<chk.name>", "Time out", t);
        case t:step(_,_,_): return notAsExpected("<chk.name>", "Trace found while no trace is expected", t);
        case t:goal(_): return notAsExpected("<chk.name>", "Trace found while no trace is expected", t);
        case t:goalInfiniteTrace(_,_,_): return notAsExpected("<chk.name>", "Trace found while no trace is expected", t);
      }
    } else {
      switch (foundTrace) {
        case t:noTrace(noSolutionFound()): return notAsExpected("<chk.name>","No trace found while trace is expected", t);
        case t:noTrace(solverTimeout()): return notAsExpected("<chk.name>", "Time out", t);
        default: return asExpected("<chk.name>");      
      }    
    }  
  } else {
    throw "Check `<chk.name>` does not have any expectations";
  }
}