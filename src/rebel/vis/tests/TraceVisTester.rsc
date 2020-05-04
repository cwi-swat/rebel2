module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::tests::ModelCheckerTester;

import rebel::checker::RebelToAlleTranslator;
import rebel::checker::Trace;
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
App[TraceVisModel] visRiverCrossingCheck(str check) = visTrace(check, |project://rebel2/examples/RiverCrossing.rebel|);

App[TraceVisModel] visPaperTransactionGetStuckCheck() = visTrace("TransactionCanGetStuck", |project://rebel2/examples/local/paper/Transaction.rebel|);
App[TraceVisModel] visPaperTransactionCanBookCheck() = visTrace("CanBookATransaction", |project://rebel2/examples/local/paper/Transaction.rebel|);

App[TraceVisModel] visPaperAccountCheck() = visTrace("CanOverdrawAccount", |project://rebel2/examples/local/paper/Account.rebel|);

App[TraceVisModel] visPaperAccountCheck() = visTrace("CanOverdrawAccount", |project://rebel2/examples/local/paper/Account.rebel|);


App[TraceVisModel] visTrace(str check, loc rebelFile) {
  Trace t = testPerformCheck(check, rebelFile);
  return createTraceVis(check, t);
}
