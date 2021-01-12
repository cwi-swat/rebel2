module rebel::checker::ExpectationRunner

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::Trace;

import rebel::checker::ModelChecker;

import util::PathUtil;

import ParseTree;
import IO;

set[str] alleAlleMods() = {"translation::Environment","translation::Relation"};


data ExpectationResult(int checkAssemblyDuration = -1, int normDuration = -1, int configBuildDuration = -1, int translateToAlleDuration = -1, int translateToSmtDuration = -1, int solveDurationSolver = -1, int solveDurationTotal = -1, int relModelCreationDuration = -1, int observedTotalDuration = -1, int nrOfSmtVars = -1, int nrOfSmtClauses = -1)
  = asExpected(str check, str config)
  | notAsExpected(str check, str config, str message, Trace trace)
  | solverTimedout(str check, str config)
  | solverError(str check, str config)
  ;

list[ExpectationResult] checkExpectations(Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true, int solverTimeout = 30 * 1000, bool countNrOfVars = false, bool countNrOfClauses = false) 
  = [checkExpectation(chk,m,tm,deps,pcfg=pcfg,saveIntermediateFiles=saveIntermediateFiles, solverTimeout=solverTimeout, countNrOfVars = countNrOfVars, countNrOfClauses = countNrOfClauses) | 
      /chk:(Check)`<Command _> <Id _> from <Id _> in <SearchDepth _> <Objectives? _> <Expect _>;` := m.parts];

ExpectationResult checkExpectation(Check chk, Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true, int solverTimeout = 30 * 1000, bool countNrOfVars = false, bool countNrOfClauses = false) {
  if (/Expect expect := chk) {
    println();
    println("Start checking expectation for `<chk.name>`");
    println("=============================");
        
    ModelCheckerResult mcr = performCheck(chk,m,tm,deps,pcfg=pcfg,saveIntermediateFiles = saveIntermediateFiles, solverTimeout = solverTimeout, countNrOfVars = countNrOfVars, countNrOfClauses = countNrOfClauses);
    
    if (/(ExpectResult)`no trace` := expect) {
      switch (mcr.t) {
        case noTrace(noSolutionFound()):  return addTiming(asExpected("<chk.name>", "<chk.config>"), mcr);
        case t:noTrace(solverTimeout()):  return addTiming(solverTimedout("<chk.name>","<chk.config>"), mcr);
        case t:step(_,_,_):               return addTiming(notAsExpected("<chk.name>", "<chk.config>", "Trace found while no trace is expected", t), mcr);
        case t:goal(_):                   return addTiming(notAsExpected("<chk.name>", "<chk.config>", "Trace found while no trace is expected", t), mcr);
        case t:goalInfiniteTrace(_,_,_):  return addTiming(notAsExpected("<chk.name>", "<chk.config>", "Trace found while no trace is expected", t), mcr);
      }
    } else {
      switch (mcr.t) {
        case t:noTrace(noSolutionFound()):  return addTiming(notAsExpected("<chk.name>", "<chk.config>","No trace found while trace is expected", t), mcr);
        case t:noTrace(solverTimeout()):    return addTiming(solverTimedout("<chk.name>","<chk.config>"), mcr);
        default:                            return addTiming(asExpected("<chk.name>", "<chk.config>"), mcr);      
      }    
    }  
  } 
  
  throw "Check `<chk.name>` does not have any expectations";
}

private ExpectationResult addTiming(ExpectationResult er, ModelCheckerResult mcr)
  = er[checkAssemblyDuration = mcr.checkAssemblyDuration][normDuration = mcr.normDuration][configBuildDuration = mcr.configBuildDuration]
      [translateToAlleDuration = mcr.translateToAlleDuration][translateToSmtDuration = mcr.translateToSmtDuration][solveDurationSolver = mcr.solveSolverDuration]
      [solveDurationTotal = mcr.solveTotal][relModelCreationDuration=mcr.constructRelModelDuration][observedTotalDuration = mcr.observedTotalDuration]
      [nrOfSmtVars = mcr.nrOfSmtVars][nrOfSmtClauses = mcr.nrOfSmtClauses];

// tuple[Trace t, int checkAssemblyDuration, int normDuration, int configBuildDuration, int translateToAlleDuration, int translateToSmtDuration, int solveSolverDuration, int solveTotal, int constructRelModelDuration, int observedTotalDuration];
str durations2str(ExpectationResult res) = 
  " - <res.observedTotalDuration> ms. (assembling: <res.checkAssemblyDuration> ms., normalization: <res.normDuration> ms., to allealle: <res.translateToAlleDuration> ms., to smt: <res.translateToSmtDuration>, solving (Z3): <res.solveDurationSolver>, solving (streaming): <res.solveDurationTotal>, construct rel model: <res.relModelCreationDuration>)";
