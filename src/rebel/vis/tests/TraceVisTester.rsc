module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::tests::ModelCheckerTester;
import rebel::checker::Trace;

import util::PathUtil;

import salix::App;

App[TraceVisModel] visCoffeeMachineCheck() = visTrace("MachineIsServing", |home:///workspace/rebel2/examples/CoffeeMachine.rebel|);
App[TraceVisModel] visHotelCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/Hotel.rebel|);
App[TraceVisModel] visRopeBridgeCheck() = visTrace("EverybodyCrossedInTheLeastTime", |home:///workspace/rebel2/examples/RopeBridge.rebel|);
App[TraceVisModel] visRingLeaderElectionCheck() = visTrace("EventuallyOneIsElected", |home:///workspace/rebel2/examples/RingLeaderElection.rebel|);
App[TraceVisModel] visLightCheck() = visTrace("BulbCanBreak", |home:///workspace/rebel2/examples/Light.rebel|);
App[TraceVisModel] visAccountCheck() = visTrace("CanBeOverdrawn", |home:///workspace/rebel2/examples/banking/Account.rebel|);
App[TraceVisModel] visDoctorCheck() = visTrace("DoctorCanGoOffCall", |home:///workspace/rebel2/examples/local/doctor/protocol/Doctor.rebel|);
App[TraceVisModel] visRiverCrossingCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/RiverCrossing.rebel|);

App[TraceVisModel] visPaperTransactionGetStuckCheck() = visTrace("TransactionCanGetStuck", |home:///workspace/rebel2/examples/local/paper/example/Transaction.rebel|);
App[TraceVisModel] visPaperTransactionCanBookCheck() = visTrace("CanBookATransaction", |home:///workspace/rebel2/examples/local/paper/example/Transaction.rebel|);

App[TraceVisModel] visPaperAccountCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/local/paper/example/Account.rebel|);

App[TraceVisModel] visTrace(str check, loc rebelFile) {
  Trace t = testPerformCheck(check, rebelFile);
  return createTraceVis(check, t);
}
