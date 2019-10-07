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
  
  translateSpecs(config(instances, initialValues, tm, 10), "exists c: Config, p: SVPingPongOnePrims | some (c |x| p) where times = 5");
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
  loc leaderFile = |project://rebel2/bin/normalized/sync/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/Follower.rebel|;
  
  //if (!exists(leaderFile)) {
    normalize(parseModule(|project://rebel2/examples/sync/Leader.rebel|));
  //}
  //if (!exists(followerFile)) {
    normalize(parseModule(|project://rebel2/examples/sync/Follower.rebel|));
  //}


  Module f = parseModule(followerFile);
  Module l = parseModule(leaderFile);

  TModel tm = rebelTModelFromTree(l, debug = true, pathConf = normPathConfig());

  instances = {<getSpec(f, "Follower"), "f1", uninitialized()>, <getSpec(l, "Leader"), "l1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 6), "exists c: Config, f: SVFollowerOnePrims, l: SVLeaderOnePrims | (some (c |x| f) where times = 2 && some (c |x| l) where times = 1)");
}
