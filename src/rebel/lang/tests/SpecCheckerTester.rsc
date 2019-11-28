module rebel::lang::tests::SpecCheckerTester

extend analysis::typepal::TestFramework;

import rebel::lang::Parser;
import rebel::lang::Syntax;
extend rebel::lang::TypeChecker;

import util::PathUtil;

import ParseTree;
import IO;

TModel check(Tree spc) = rebelTModelFromTree(spc, debug=true, pathConf = pathConfig(srcs=[], lib=[]));
  
bool runRebelTests()
  = runTests([|project://rebel2/src/rebel/lang/tests/tests.ttl|], #Module, check);

TModel checkSpec(loc spc) = rebelTModelFromTree(parseModule(spc), debug=true, pathConf = pathConfig(srcs=[ project(spc) + "src", project(spc) + "examples"], lib=[]));
