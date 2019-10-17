module rebel::lang::tests::SpecCheckerTester

extend rebel::lang::SpecTypeChecker;
extend analysis::typepal::TestFramework;

import rebel::lang::SpecParser;
import rebel::lang::SpecSyntax;

import ParseTree;
import IO;

TModel check(Tree spc) = rebelTModelFromTree(spc, debug=true, pathConf = pathConfig(src=[], lib=[]));
  
bool runRebelTests()
  = runTests([|project://rebel2/src/rebel/lang/tests/tests.ttl|], #Module, check);
