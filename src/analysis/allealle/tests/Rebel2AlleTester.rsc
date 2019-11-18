module analysis::allealle::tests::Rebel2AlleTester

import analysis::allealle::Rebel2Alle;
import analysis::allealle::ConfigTranslator;
import analysis::allealle::LTLTranslator;
import analysis::allealle::SyncedEventGraphBuilder;

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;

import analysis::allealle::CommonTranslationFunctions;

import String;
import IO;
import List;
import ParseTree;

import analysis::Normalizer;
import util::PathUtil;
import analysis::graphs::Graph;

void translatePingPong()                  = performCheck("HitFiveTimes", parseModule(|project://rebel2/examples/PingPong.rebel|));
void translateCoffeeMachine()             = performCheck("MachineIsServing", parseModule(|project://rebel2/examples/CoffeeMachine.rebel|));
void translateLeaderAndFollower()         = performCheck("UniqueFollower", parseModule(|project://rebel2/examples/sync/double/Leader.rebel|));
void translateHotel()                     = performCheck("NoIntruder", parseModule(|project://rebel2/examples/Hotel.rebel|));
void translateRopeBridge()                = performCheck("EverybodyCrossedInTheLeastTime", parseModule(|project://rebel2/examples/RopeBridge.rebel|));
void translateLeaderElection(str check)   = performCheck(check, parseModule(|project://rebel2/examples/RingLeaderElection.rebel|));  
void translateId()                        = performCheck("ConsecutiveValues", parseModule(|project://rebel2/examples/lib/checks/IdChecks.rebel|));  
