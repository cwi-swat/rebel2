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

void translatePingPong() {
  Module pp = normalize(parseModule(|project://rebel2/examples/pingpong.rebel|));
  
  TModel tm = rebelTModelFromTree(pp);
    
  instances = {<pp.spc, "p1", uninitialized()>, <pp.spc, "p2", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, 10), tm, "exists c: Config, p: SVPingPongOnePrims | some (c |x| p) where times = 5");
}

void translateCoffeeMachine() {
  Module c = normalize(parseSpec(|project://rebel2/examples/CoffeeMachine.rebel|));
  
  TModel tm = rebelTModelFromTree(c);
    
  instances = {<c.spc, "cm1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, 10), tm, "exists c: Config | (c |x| instanceInState)[state] in StateCoffeeMachineServe");
}

void translateLeaderAndFollower() {
  Module f = normalize(parseSpec(|project://rebel2/examples/sync/follower.rebel|));
  Module l = normalize(parseSpec(|project://rebel2/examples/sync/leader.rebel|));

  TModel tm = rebelTModelFromTree(f);

  instances = {<f.spc, "f1", uninitialized()>, <l.spc, "l1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, 6), tm, "exists c: Config, f: SVFollowerOnePrims, l: SVLeaderOnePrims | (some (c |x| f) where times = 2 && some (c |x| l) where times = 1)");
}
