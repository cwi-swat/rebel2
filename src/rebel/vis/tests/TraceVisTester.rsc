module rebel::vis::tests::TraceVisTester

import rebel::vis::TraceVis;

import rebel::checker::tests::ModelCheckerTester;

import salix::App;

private loc root() = |home:///develop/workspace/personal/|;

App[TraceVisModel] visCoffeeMachineCheck(str check) = visTrace(check, root() + "rebel2/examples/CoffeeMachine.rebel", timeout = 0);
App[TraceVisModel] visHotelCheck(str check) = visTrace(check, |home:///develop/workspace/personal/rebel2/examples/paper/performance/rebel/Hotel.rebel|);
App[TraceVisModel] visRopeBridgeCheck() = visTrace("EverybodyCrossedInTheLeastTime", |home:///workspace/rebel2/examples/RopeBridge.rebel|);
App[TraceVisModel] visRingLeaderElectionCheck() = visTrace("EventuallyOneIsElected", |project://rebel2/examples/paper/performance/rebel/RingLeaderElection.rebel|);
App[TraceVisModel] visLightCheck() = visTrace("BulbCanBreak", |project://rebel2/examples/Light.rebel|);
App[TraceVisModel] visAccountCheck() = visTrace("CantOverdrawAccount", |project://rebel2/examples/paper/example/Account.rebel|);
App[TraceVisModel] visDoctorCheck() = visTrace("DoctorCanGoOffCall", |home:///workspace/rebel2/examples/local/doctor/protocol/Doctor.rebel|);
App[TraceVisModel] visRiverCrossingCheck(str check) = visTrace(check, |home:///workspace/rebel2/examples/paper/performance/rebel/RiverCrossing.rebel|);

App[TraceVisModel] visPaperTransactionDontGetStuckCheck() = visTrace("TransactionsDontGetStuck", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);
App[TraceVisModel] visPaperTransactionCanBookRun() = visTrace("CanBookATransaction", |home:///workspace/rebel2/examples/paper/example/Transaction.rebel|);

App[TraceVisModel] visPaperAccountCheck(str check) = visTrace(check, |project://rebel2/examples/paper/example/Account.rebel|);

App[TraceVisModel] visTrace(str check, loc rebelFile, int timeout = 30 * 1000, bool saveIntermediateFiles = true) {
  //alias ModelCheckerTesterResult = tuple[ModelCheckerResult mcr, TModel tm, str config, str moduleName];
  ModelCheckerTesterResult result = testPerformCheck(check, rebelFile, timeout = timeout, saveIntermediateFiles = saveIntermediateFiles);
  return createTraceVis(check, result.config, result.moduleName, result.mcr.t);
}
