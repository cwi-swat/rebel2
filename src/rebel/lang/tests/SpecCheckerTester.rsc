module rebel::lang::tests::SpecCheckerTester

extend analysis::typepal::TestFramework;

import rebel::lang::Parser;
import rebel::lang::Syntax;
extend rebel::lang::TypeChecker;

import ParseTree;
import IO;

TModel check(Tree spc) = rebelTModelFromTree(spc, debug=true, pathConf = pathConfig(srcs=[], lib=[]));
  
bool runRebelTests()
  = runTests([|project://rebel2/src/rebel/lang/tests/tests.ttl|], #Module, check);

void checkSpec(loc spc) {
  Module m = parseModule(spc);
  TModel model = rebelTModelFromTree(m, debug=true, pathConf = pathConfig(srcs=[|project://rebel2/examples|], lib=[]));
}  