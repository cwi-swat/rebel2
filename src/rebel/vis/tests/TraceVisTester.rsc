module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::tests::ModelCheckerTester;

import salix::App;

App[TraceVisModel] visCoffeeMachineCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/CoffeeMachine.rebel|);
App[TraceVisModel] visHotelCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/performance/rebel/Hotel.rebel|);
App[TraceVisModel] visRopeBridgeCheck() = visTrace("EverybodyCrossedInTheLeastTime", |home:///workspace/rebel2/examples/RopeBridge.rebel|);
App[TraceVisModel] visRingLeaderElectionCheck() = visTrace("EventuallyOneIsElected", |home:///workspace/rebel2/examples/paper/performance/rebel/RingLeaderElection.rebel|);
App[TraceVisModel] visLightCheck() = visTrace("BulbCanBreak", |home:///workspace/rebel2/examples/Light.rebel|);
App[TraceVisModel] visAccountCheck() = visTrace("CanBeOverdrawn", |home:///workspace/rebel2/examples/banking/Account.rebel|);
App[TraceVisModel] visDoctorCheck() = visTrace("DoctorCanGoOffCall", |home:///workspace/rebel2/examples/local/doctor/protocol/Doctor.rebel|);
App[TraceVisModel] visRiverCrossingCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/performance/rebel/RiverCrossing.rebel|);

App[TraceVisModel] visPaperTransactionDontGetStuckCheck() = visTrace("TransactionsDontGetStuck", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);
App[TraceVisModel] visPaperTransactionCanBookRun() = visTrace("CanBookATransaction", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);

App[TraceVisModel] visPaperAccountCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/example/Account.rebel|);

App[TraceVisModel] visTrace(str check, loc rebelFile, int timeout = 30 * 1000) {
  //alias ModelCheckerTesterResult = tuple[ModelCheckerResult mcr, TModel tm, str config, str moduleName];
  ModelCheckerTesterResult result = testPerformCheck(check, rebelFile, timeout = timeout);
  return createTraceVis(check, result.config, result.moduleName, result.mcr.t);
}
