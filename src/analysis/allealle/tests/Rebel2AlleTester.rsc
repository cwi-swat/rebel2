module analysis::allealle::tests::Rebel2AlleTester

import analysis::allealle::Rebel2Alle;
import analysis::allealle::SyncedEventGraphBuilder;

import rebel::lang::SpecSyntax;
import rebel::lang::SpecParser;
import rebel::lang::SpecTypeChecker;

import analysis::allealle::CommonTranslationFunctions;

import String;
import IO;
import List;
import ParseTree;

import analysis::Normalizer;
import util::PathUtil;
import analysis::graphs::Graph;

void translatePingPong() {
  Module pp = parseModule(|project://rebel2/examples/PingPong.rebel|);
  normalize(pp);
  
  Module normalizedPp = parseModule(|project://rebel2/bin/normalized/PingPong.rebel|);
  
  TModel tm = rebelTModelFromTree(normalizedPp, pathConf = normPathConfig());
    
  instances = {<getSpec(normalizedPp, "PingPong"), "p1", uninitialized()>, 
               <getSpec(normalizedPp, "PingPong"), "p2", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 8), "exists c: Config, p: PingPongTimes | some (c |x| p) where times = 5");
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
    
  instances = {<getSpec(normalizedCm, "CoffeeMachine"), "cm1", uninitialized()>,
               <getSpec(normalizedCm, "CoffeeMachine"), "cm2", uninitialized()>,
               <getSpec(normalizedCm, "CoffeeMachine"), "cm3", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 10), "exists c: Config, cm: (Instance ⨝ CoffeeMachine)[instance] | (c ⨝ instanceInState ⨝ cm)[state] in StateCoffeeMachineServe");
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
  
  translateSpecs(config(instances, initialValues, tm, 7), "∃ c ∈ Config, f ∈ FollowerTimes, l ∈ LeaderTimes | (some (c ⨝ f) where times = 2 ∧ some (c ⨝ l) where times = 2)");
}

void translateLeaderFollowerAndTailer() {
  loc leaderFile = |project://rebel2/bin/normalized/sync/triple/Leader.rebel|;
  loc followerFile = |project://rebel2/bin/normalized/sync/triple/Follower.rebel|;
  loc tailerFile = |project://rebel2/bin/normalized/sync/triple/Tailer.rebel|;
  
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
    "∃ c ∈ Config | (some (c ⨝ LeaderTimes) where times = 2)
    'exists c: Config | forall l : (Instance |x| Leader)[instance] | (l |x| instanceInState |x| c)[state] in initialized");
}

void translateMultiFollowers() {
  loc followerFile = |project://rebel2/bin/normalized/sync/multi/Follower.rebel|;
  loc leaderFile = |project://rebel2/bin/normalized/sync/multi/Leader.rebel|;
  
  Module f = parseModule(|project://rebel2/examples/sync/multi/Follower.rebel|);
  Module l = parseModule(|project://rebel2/examples/sync/multi/Leader.rebel|);
  
  normalize(f);
  normalize(l);

  Module normalizedF = parseModule(followerFile);
  Module normalizedL = parseModule(leaderFile);

  TModel tm = rebelTModelFromTree(normalizedL, debug = false, pathConf = normPathConfig());

  instances = {<getSpec(normalizedF, "Follower"), "f1", uninitialized()>, 
               <getSpec(normalizedF, "Follower"), "f2", uninitialized()>,
               <getSpec(normalizedF, "Follower"), "f3", uninitialized()>,
               <getSpec(normalizedL, "Leader"), "l1", uninitialized()>};
               
  initialValues = {};  
  
  translateSpecs(config(instances, initialValues, tm, 11), "∃ c ∈ Config, l ∈ (Instance ⨝ Leader)[instance] | ((some (LeaderFollowers ⨝ c ⨝ l)[count() as nr] where nr = 3))
                                                           '∃ c ∈ Config | (some (c |x| LeaderNrOfHits) where nrOfHits = 2)");
}

void translateHotel() {
  normalize(parseModule(|project://rebel2/examples/Hotel.rebel|));
  
  Module normalizedHotel = parseModule(|project://rebel2/bin/normalized/Hotel.rebel|);
  
  TModel tm = rebelTModelFromTree(normalizedHotel, debug = false, pathConf = normPathConfig());
  
  instances = {<getSpec(normalizedHotel, "Room"), "r1", uninitialized()>, 
               <getSpec(normalizedHotel, "Guest"), "g1", uninitialized()>,
               <getSpec(normalizedHotel, "Guest"), "g2", uninitialized()>,
               <getSpec(normalizedHotel, "Key"), "k1", uninitialized()>,
               <getSpec(normalizedHotel, "Key"), "k2", uninitialized()>,
               <getSpec(normalizedHotel, "Key"), "k3", uninitialized()>,
               <getSpec(normalizedHotel, "Card"), "ca1", uninitialized()>,
               <getSpec(normalizedHotel, "Card"), "ca2", uninitialized()>,
               <getSpec(normalizedHotel, "Card"), "ca3", uninitialized()>,
               <getSpec(normalizedHotel, "FrontDesk"), "fd1", uninitialized()>};

  initialValues = {};

  str noIntruder = "∃ step1 ∈ order, g1 ∈ (Guest ⨝ Instance)[instance], g2 ∈ ((Guest ⨝ Instance)[instance] ∖ g1) | let step2 = (order ⨝ step1[nxt-\>cur]), step3 = (order ⨝ step2[nxt-\>cur]) | 
                   '  ((raisedEvent ⨝ step1)[instance,event] = (g1 ⨯ EventGuestEnterRoom) ∧ 
                   '   (raisedEvent ⨝ step2)[instance,event] = (g2 ⨯ EventGuestEnterRoom) ∧ 
                   '   (raisedEvent ⨝ step3)[instance,event] = (g1 ⨯ EventGuestEnterRoom))";  
  
  str twoGuestsWithSameCard = "∃ c ∈ Config, g1 ∈ (Guest ⨝ Instance)[instance], g2 ∈ (Guest ⨝ Instance)[instance] ∖ g1 | ((g1 ⨝ instanceInState ⨝ c)[state] ⊆ initialized ∧ (GuestCard ⨝ c ⨝ g1)[card] = (GuestCard ⨝ c ⨝ g2)[card])";  
  
  str twoCheckedInGuests = "∃ c ∈ Config, g1 ∈ (Guest ⨝ Instance)[instance], g2 ∈ (Guest ⨝ Instance)[instance] ∖ g1 | ((g1 ⨝ instanceInState ⨝ c)[state] ⊆ initialized ∧ (g2 ⨝ instanceInState ⨝ c)[state] ⊆ initialized)";
   
  translateSpecs(config(instances, initialValues, tm, 12), noIntruder);
}

void translateRopeBridge() {
  normalize(parseModule(|project://rebel2/examples/RopeBridge.rebel|));
  
  Module normalizedRB = parseModule(|project://rebel2/bin/normalized/RopeBridge.rebel|);
  
  TModel tm = rebelTModelFromTree(normalizedRB, debug = false, pathConf = normPathConfig());
  
  instances = {<getSpec(normalizedRB, "Traveller"), "t1", state("near")>,
               <getSpec(normalizedRB, "Traveller"), "t2", state("near")>,
                <getSpec(normalizedRB, "Traveller"), "t3", state("near")>,
                <getSpec(normalizedRB, "Traveller"), "t4", state("near")>,
               <getSpec(normalizedRB, "FlashLight"), "fl1", state("near")>};

  initialValues = {<getSpec(normalizedRB, "Traveller"), "t1", "timeToCross", "1">,
                   <getSpec(normalizedRB, "Traveller"), "t2", "timeToCross", "2">,
                   <getSpec(normalizedRB, "Traveller"), "t3", "timeToCross", "5">,
                   <getSpec(normalizedRB, "Traveller"), "t4", "timeToCross", "10">,
                   <getSpec(normalizedRB, "FlashLight"), "fl1", "totalTimeSpend", "0">};

  str everyBodyCrossed = "exists c: Config | ((forall t ∈ (Instance ⨝ Traveller)[instance] | (instanceInState ⨝ t ⨝ c)[state] ⊆ StateTravellerFar) && (some (FlashLightTotalTimeSpend |x| c) where totalTimeSpend = 17))"; 
   
  translateSpecs(config(instances, initialValues, tm, 7), everyBodyCrossed);
}
