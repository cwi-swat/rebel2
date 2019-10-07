module analysis::tests::CheckerTester

extend analysis::Checker;
extend analysis::typepal::TestFramework;

import lang::Parser;
import lang::Syntax;
import util::Reflective;

import ParseTree;
import IO;

TModel checkPingpong() 
  = collectAndSolve(parseModule(|project://rebel2/examples/pingpong.rebel|));

TModel checkCoffeeMachine() 
  = collectAndSolve(parseModule(|project://rebel2/examples/CoffeeMachine.rebel|));

TModel checkNormalizedCoffeeMachine() 
  = collectAndSolve(parseModule(|project://rebel2/bin/normalized/CoffeeMachine.rebel|));

TModel check(Tree spc) = rebelTModelFromTree(spc, debug=true, pathConf = pathConfig(src=[], lib=[]));
  
bool runRebelTests()
  = runTests([|project://rebel2/src/analysis/tests/tests.ttl|], #Module, check);
