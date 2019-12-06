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

void checkAllInDir(loc base) {
  
}

void translatePingPong(str check)         = performCheck(check, parseModule(|project://rebel2/examples/PingPong.rebel|));
void translateCoffeeMachine()             = performCheck("MachineIsServing", parseModule(|project://rebel2/examples/CoffeeMachine.rebel|));
void translateLeaderAndFollower(str check) = performCheck(check, parseModule(|project://rebel2/examples/sync/double/Leader.rebel|));
void translateMultiFollower(str check)    = performCheck(check, parseModule(|project://rebel2/examples/sync/multi/Leader.rebel|));
void translateHotel()                     = performCheck("NoIntruder", parseModule(|project://rebel2/examples/Hotel.rebel|));
void translateRopeBridge()                = performCheck("EverybodyCrossedInTheLeastTime", parseModule(|project://rebel2/examples/RopeBridge.rebel|));
void translateLeaderElection(str check)   = performCheck(check, parseModule(|project://rebel2/examples/RingLeaderElection.rebel|));  
void translateId()                        = performCheck("ConsecutiveValues", parseModule(|project://rebel2/examples/lib/checks/IdChecks.rebel|));
void translateLight(str check)            = performCheck(check, parseModule(|project://rebel2/examples/Light.rebel|)); 
void translateDate(str check)             = performCheck(check, parseModule(|project://rebel2/examples/Date.rebel|)); 
void translateABP(str check)              = performCheck(check, parseModule(|project://rebel2/examples/AlternatingBitProtocol.rebel|));

void translateDebitCard(str check)        = performCheck(check, parseModule(|project://rebel2/examples/local/debitcard/DebitCard.rebel|));

void translate(loc rebelFile, str check)  = performCheck(check, parseModule(rebelFile)); 
