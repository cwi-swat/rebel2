module rebel::checker::tests::ModelCheckerTester

import rebel::checker::ModelChecker;
import rebel::checker::Trace;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;
import util::PathUtil;

alias ModelCheckerTesterResult = tuple[ModelCheckerResult mcr, TModel tm, str config, str moduleName]; 

ModelCheckerTesterResult testPerformCheckOnCoffeeMachine() = testPerformCheck("CanServeNormalCoffee", |project://rebel2/examples/CoffeeMachine.rebel|);

ModelCheckerTesterResult testPerformCheckOnTransaction1() = testPerformCheck("CanBookATransaction", |project://rebel2/examples/paper/example/Transaction.rebel|);
ModelCheckerTesterResult testPerformCheckOnTransaction2() = testPerformCheck("TransactionCanGetStuck", |project://rebel2/examples/paper/exampleTransaction.rebel|);

ModelCheckerTesterResult testPerformCheckOnHotel() = testPerformCheck("NoIntruder", |project://rebel2/examples/paper/performance/rebel/Hotel.rebel|);
ModelCheckerTesterResult testPerformCheckOnLight() = testPerformCheck("BulbCanBreak", |project://rebel2/examples/Light.rebel|);

ModelCheckerTesterResult testPerformCheck(str check, loc spec, int timeout = 30 * 1000) {
  PathConfig pcfg = defaultPathConfig(spec);
  
  Module m = parseModule(spec);
  TypeCheckerResult tcr = checkModule(m, calculateDependencies(m,pcfg), pcfg); 
  
  Check chk = findCheckByName(check, m);
  return <performCheck(chk, m, tcr.tm, tcr.depGraph, pcfg = pcfg, saveIntermediateFiles = true, solverTimeout = timeout), tcr.tm, "<chk.config>", "<m.\module.name>">;
}

private Check findCheckByName(str check, Module m) {
  if ((Part)`<Check chk>` <- m.parts, "<chk.name>" == check) {
    return chk;
  }
  
  throw "Unable to find check with name `<check>`"; 
}

