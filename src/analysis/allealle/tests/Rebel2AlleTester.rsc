module analysis::allealle::tests::Rebel2AlleTester

import analysis::allealle::Rebel2Alle;

import lang::Syntax;
import lang::Parser;

import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;

import String;
import IO;
import List;
import ParseTree;

import analysis::Normalizer;
import util::PathUtil;

void translatePingPong() {
  Module pp = parseModule(|project://rebel2/examples/pingpong.rebel|);
  Module normalizedPp = normalize(pp);
  
  TModel tm = rebelTModelFromTree(normalizedPp, pathConf = normPathConfig());
  
  instances = {<getSpec(normalizedPp, "PingPong"), "p1", uninitialized()>, 
               <getSpec(normalizedPp, "PingPong"), "p2", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 8), "exists c: Config, p: SVPingPongOnePrims | some (c |x| p) where times = 5");
}

private PathConfig normPathConfig() = pathConfig(srcs=[|project://rebel2/bin/normalized|]);

Spec getSpec(Module m, str specName) {
  for ((Part)`<Spec spc>` <- m.parts, "<spc.name>" == specName) {
    return spc;
  }
  
  throw "Unable to find spec with name `<specName>` in file `<m@\loc.top>`"; 
}

void translateCoffeeMachine() {
  loc specFile = |project://rebel2/bin/normalized/CoffeeMachine.rebel|;
  
  Module cm = parseModule(|project://rebel2/examples/CoffeeMachine.rebel|);
  normalize(cm);
  
  Module normalizedCm = parseModule(specFile); 
  
  TModel tm = rebelTModelFromTree(normalizedCm, pathConf = normPathConfig());
    
  instances = {<getSpec(normalizedCm, "CoffeeMachine"), "cm1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 10), "exists c: Config | (c |x| instanceInState)[state] in StateCoffeeMachineServe");
}

void translateLeaderAndFollower() {
  loc leaderFile = |project://rebel2/bin/normalized/sync/double/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/double/Follower.rebel|;
  
  Module f = parseModule(|project://rebel2/examples/sync/double/Follower.rebel|);
  Module l = parseModule(|project://rebel2/examples/sync/double/Leader.rebel|);
  
  normalize(f);
  normalize(l);

  Module normalizedF = parseModule(followerFile);
  Module normalizedL = parseModule(leaderFile);

  TModel tm = rebelTModelFromTree(normalizedL, debug = false, pathConf = normPathConfig());

  instances = {<getSpec(normalizedF, "Follower"), "f1", uninitialized()>, 
               <getSpec(normalizedF, "Follower"), "f2", uninitialized()>, 
               <getSpec(normalizedL, "Leader"), "l1", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 6), "∃ c ∈ Config, f ∈ SVFollowerOnePrims, l ∈ SVLeaderOnePrims | (some (c ⨝ f) where times = 3 ∧ some (c ⨝ l) where times = 3)");
}

void translateLeaderFollowerAndTailer() {
  loc leaderFile = |project://rebel2/bin/normalized/sync/triple/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/triple/Follower.rebel|;
  loc tailerFile = |project://rebel2/bin/normalized/sync/triple/Tailer.rebel|;
  
  Module l = parseModule(leaderFile);
  Module f = parseModule(followerFile);
  Module t = parseModule(tailerFile);
  
  normalize(parseModule(|project://rebel2/examples/sync/triple/Leader.rebel|));
  normalize(parseModule(|project://rebel2/examples/sync/triple/Follower.rebel|));
  normalize(parseModule(|project://rebel2/examples/sync/triple/Tailer.rebel|));

  Module normalizedL = parseModule(leaderFile);
  Module normalizedF = parseModule(followerFile);
  Module normalizedT = parseModule(tailerFile);

  TModel tm = rebelTModelFromTree(normalizedL, debug = false, pathConf = normPathConfig());

  instances = {<getSpec(normalizedF, "Follower"), "f1", uninitialized()>, 
               <getSpec(normalizedF, "Follower"), "f2", uninitialized()>, 
               <getSpec(normalizedT, "Tailer"), "t1", uninitialized()>,
               <getSpec(normalizedT, "Tailer"), "t2", uninitialized()>,
               <getSpec(normalizedL, "Leader"), "l1", uninitialized()>,
               <getSpec(normalizedL, "Leader"), "l2", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 9), 
    "∃ c ∈ Config | (some (c ⨝ SVLeaderOnePrims) where times = 2)
    'exists c: Config | forall l : (Instance |x| Leader)[instance] | (l |x| instanceInState |x| c)[state] in initialized");
}
