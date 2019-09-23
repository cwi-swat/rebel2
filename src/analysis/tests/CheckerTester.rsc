module analysis::tests::CheckerTester

extend analysis::Checker;
extend analysis::typepal::TestFramework;

import lang::Parser;
import lang::Syntax;

import ParseTree;
import IO;

TModel checkPingpong() 
  = collectAndSolve(parseSpec(|project://rebel2/examples/pingpong.rebel|));

TModel checkCoffeeMachine() 
  = collectAndSolve(parseSpec(|project://rebel2/examples/CoffeeMachine.rebel|));
