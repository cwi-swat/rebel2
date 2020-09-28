module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::tests::ModelCheckerTester;
import rebel::checker::Trace;

import util::PathUtil;

import salix::App;

App[TraceVisModel] visCoffeeMachineCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/CoffeeMachine.rebel|);
App[TraceVisModel] visHotelCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/performance/rebel/Hotel.rebel|);
App[TraceVisModel] visRopeBridgeCheck() = visTrace("EverybodyCrossedInTheLeastTime", |home:///workspace/rebel2/examples/RopeBridge.rebel|);
App[TraceVisModel] visRingLeaderElectionCheck() = visTrace("EventuallyOneIsElected", |home:///workspace/rebel2/examples/RingLeaderElection.rebel|);
App[TraceVisModel] visLightCheck() = visTrace("BulbCanBreak", |home:///workspace/rebel2/examples/Light.rebel|);
App[TraceVisModel] visAccountCheck() = visTrace("CanBeOverdrawn", |home:///workspace/rebel2/examples/banking/Account.rebel|);
App[TraceVisModel] visDoctorCheck() = visTrace("DoctorCanGoOffCall", |home:///workspace/rebel2/examples/local/doctor/protocol/Doctor.rebel|);
App[TraceVisModel] visRiverCrossingCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/RiverCrossing.rebel|);

App[TraceVisModel] visPaperTransactionDontGetStuckCheck() = visTrace("TransactionsDontGetStuck", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);
App[TraceVisModel] visPaperTransactionCanBookRun() = visTrace("CanBookATransaction", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);

App[TraceVisModel] visPaperAccountCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/example/Account.rebel|);

App[TraceVisModel] visTrace(str check, loc rebelFile, int timeout = 30 * 1000) {
  Trace t = testPerformCheck(check, rebelFile, timeout = timeout);
  return createTraceVis(check, t);
}
