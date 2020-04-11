module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::Rebel2Alle;
import rebel::checker::RebelTrace;
import rebel::lang::Syntax;
import rebel::lang::Parser;

import util::PathUtil;
import ParseTree;

import salix::App;

App[TraceVisModel] visCoffeeMachineCheck() = visTrace("MachineIsServing", |project://rebel2/examples/CoffeeMachine.rebel|);
App[TraceVisModel] visHotelCheck(str check) = visTrace(check, |project://rebel2/examples/Hotel.rebel|);
App[TraceVisModel] visRopeBridgeCheck() = visTrace("EverybodyCrossedInTheLeastTime", |project://rebel2/examples/RopeBridge.rebel|);
App[TraceVisModel] visRingLeaderElectionCheck() = visTrace("EventuallyOneIsElected", |project://rebel2/examples/RingLeaderElection.rebel|);
App[TraceVisModel] visLightCheck() = visTrace("BulbCanBreak", |project://rebel2/examples/Light.rebel|);
App[TraceVisModel] visAccountCheck() = visTrace("CanBeOverdrawn", |project://rebel2/examples/banking/Account.rebel|);
App[TraceVisModel] visDoctorCheck() = visTrace("DoctorCanGoOffCall", |project://rebel2/examples/local/doctor/protocol/Doctor.rebel|);
App[TraceVisModel] visPaperTransactionCheck() = visTrace("TransactionCanGetStuck", |project://rebel2/examples/local/paper/Transaction.rebel|);

App[TraceVisModel] visTrace(str check, loc rebelFile) {
  Module m = parseModule(rebelFile);

  PathConfig pcfg = defaultPathConfig(m@\loc.top);
  PathConfig normPcfg = normalizerPathConfig(m@\loc.top);

  Trace t = performCheck(check, m, pcfg, normPcfg);
  
  return createTraceVis(check, t);
}
