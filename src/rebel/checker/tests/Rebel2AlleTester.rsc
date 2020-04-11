module rebel::checker::tests::Rebel2AlleTester

import rebel::checker::Rebel2Alle;
import rebel::checker::Normalizer;
import util::PathUtil;

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import ParseTree;

void checkAllInDir(loc base) {
  
}

void checkPingPong(str check)         = runCheck(check, |project://rebel2/examples/PingPong.rebel|);
void translateCoffeeMachine()             = performCheck("MachineIsServing", parseModule(|project://rebel2/examples/CoffeeMachine.rebel|));
void translateLeaderAndFollower(str check) = performCheck(check, parseModule(|project://rebel2/examples/sync/double/Leader.rebel|));
void translateMultiFollower(str check)    = performCheck(check, parseModule(|project://rebel2/examples/sync/multi/Leader.rebel|));
void translateHotel()                     = performCheck("NoIntruder", parseModule(|project://rebel2/examples/Hotel.rebel|));
void translateRopeBridge()                = performCheck("EverybodyCrossedInTheLeastTime", parseModule(|project://rebel2/examples/RopeBridge.rebel|));
void translateLeaderElection(str check)   = performCheck(check, parseModule(|project://rebel2/examples/RingLeaderElection.rebel|));  
void translateId()                        = performCheck("ConsecutiveValues", parseModule(|project://rebel2/examples/lib/checks/IdChecks.rebel|));
void translateLight(str check)            = performCheck(check, parseModule(|project://rebel2/examples/Light.rebel|)); 
void translateDate(str check)             = performCheck(check, parseModule(|project://rebel2/examples/Date.rebel|)); 
void translateABP(str check)              = performCheck(check, parseModule(|project://rebel2/examples/AlternatingBitProtocol.rebel|));

void translateDebitCard(str check)        = performCheck(check, parseModule(|project://rebel2/examples/local/debitcard/DebitCard.rebel|));

void translate(loc rebelFile, str check)  = performCheck(check, parseModule(rebelFile)); 

void createSnippets(loc rebelFile) {
  Module m = parseModule(rebelFile);

  PathConfig pcfg = defaultPathConfig(m@\loc.top);
  PathConfig normPcfg = normalizerPathConfig(m@\loc.top);
          
  Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
  if (/unresolvedModule(QualifiedName qfn) := depGraph) {
    println("`<qfn>` could not be resolved yet, stopped the building process");
    return;
  }
  
  NormalizedResult nr = normalizeAndCheck(m, depGraph, pcfg, normPcfg);
  translateSnippets(nr.normMod, nr.normDepGraph, normPcfg);    
}

void runCheck(str check, loc rebelFile) {
  Module m = parseModule(rebelFile);

  PathConfig pcfg = defaultPathConfig(m@\loc.top);
  PathConfig normPcfg = normalizerPathConfig(m@\loc.top);

  performCheck(check, m, pcfg, normPcfg);
}

void runCleanCheck(str check, loc rebelFile) {
  
}
