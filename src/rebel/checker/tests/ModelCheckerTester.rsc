module rebel::checker::tests::ModelCheckerTester

import rebel::checker::ModelChecker;
import rebel::checker::Trace;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import util::PathUtil;

Trace testPerformCheckOnCoffeeMachine() = testPerformCheck("CanServeNormalCoffee", |project://rebel2/examples/CoffeeMachine.rebel|);

Trace testPerformCheckOnTransaction1() = testPerformCheck("CanBookATransaction", |project://rebel2/examples/local/paper/Transaction.rebel|);
Trace testPerformCheckOnTransaction2() = testPerformCheck("TransactionCanGetStuck", |project://rebel2/examples/local/paper/Transaction.rebel|);

Trace testPerformCheckOnHotel() = testPerformCheck("NoIntruder", |project://rebel2/examples/Hotel.rebel|);

Trace testPerformCheckOnLight() = testPerformCheck("BulbCanBreak", |project://rebel2/examples/Light.rebel|);

Trace testPerformCheck(str check, loc spec, int timeout = 30 * 1000) {
  PathConfig pcfg = defaultPathConfig(spec);
  
  Module m = parseModule(spec);
  TypeCheckerResult tcr = checkModule(m, calculateDependencies(m,pcfg), pcfg); 
  
  Check chk = findCheckByName(check, tcr.depGraph);
  return performCheck(chk, m, tcr.tm, tcr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = timeout);
}

private Check findCheckByName(str check, Graph[RebelDependency] modDep) {
  if (/resolvedAndCheckedModule(Module m, TModel tm, _) := modDep, /Check chk := m, "<chk.name>" == check) {
    return chk;
  }
  
  throw "Unable to find check with name `<check>`"; 
}

