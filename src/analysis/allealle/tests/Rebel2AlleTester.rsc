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
  Module ppm = normalize(parseModule(|project://rebel2/examples/pingpong.rebel|));
  
  TModel tm = rebelTModelFromTree(ppm, pathConf = normPathConfig());
  
  Spec pp = getSpec(ppm, "PingPong");
    
  instances = {<pp, "p1", uninitialized()>, <pp, "p2", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 20), "exists c: Config, p: SVPingPongOnePrims | some (c |x| p) where times = 5");
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
  
  if (!exists(specFile)) {
    normalize(parseModule(|project://rebel2/examples/CoffeeMachine.rebel|));
  }
  
  Module c = parseModule(specFile); 
  
  TModel tm = rebelTModelFromTree(c, pathConf = normPathConfig());
    
  instances = {<getSpec(c, "CoffeeMachine"), "cm1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 10), "exists c: Config | (c |x| instanceInState)[state] in StateCoffeeMachineServe");
}

void translateLeaderAndFollower() {
  loc leaderFile = |project://rebel2/bin/normalized/sync/double/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/double/Follower.rebel|;
  
  normalize(parseModule(|project://rebel2/examples/sync/double/Leader.rebel|));
  normalize(parseModule(|project://rebel2/examples/sync/double/Follower.rebel|));

  Module f = parseModule(followerFile);
  Module l = parseModule(leaderFile);

  TModel tm = rebelTModelFromTree(l, debug = false, pathConf = normPathConfig());

  instances = {<getSpec(f, "Follower"), "f1", uninitialized()>, <getSpec(f, "Follower"), "f2", uninitialized()>, <getSpec(l, "Leader"), "l1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 6), "∃ c ∈ Config, f ∈ SVFollowerOnePrims, l ∈ SVLeaderOnePrims | (some (c ⨝ f) where times = 3 ∧ some (c ⨝ l) where times = 3)");
}

void translateLeaderFollowerAndTailer() {
  loc leaderFile = |project://rebel2/bin/normalized/sync/triple/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/triple/Follower.rebel|;
  loc tailerFile = |project://rebel2/bin/normalized/sync/triple/Tailer.rebel|;
  
  normalize(parseModule(|project://rebel2/examples/sync/triple/Leader.rebel|));
  normalize(parseModule(|project://rebel2/examples/sync/triple/Follower.rebel|));
  normalize(parseModule(|project://rebel2/examples/sync/triple/Tailer.rebel|));

  Module l = parseModule(leaderFile);
  Module f = parseModule(followerFile);
  Module t = parseModule(tailerFile);

  TModel tm = rebelTModelFromTree(l, debug = false, pathConf = normPathConfig());

  instances = {<getSpec(f, "Follower"), "f1", uninitialized()>, 
               <getSpec(f, "Follower"), "f2", uninitialized()>, 
               <getSpec(t, "Tailer"), "t1", uninitialized()>,
               <getSpec(l, "Leader"), "l1", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 10), "∃ c ∈ Config | (some (c ⨝ SVLeaderOnePrims) where times = 2)");
}
