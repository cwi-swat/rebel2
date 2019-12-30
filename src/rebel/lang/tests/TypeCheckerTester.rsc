module rebel::lang::tests::TypeCheckerTester

extend analysis::typepal::TestFramework;

import rebel::lang::Parser;
import rebel::lang::Syntax;
extend rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import util::PathUtil;

import ParseTree;
import IO;

TModel check(Tree t, bool saveTModels = false, PathConfig pcfg = pathConfig(srcs=[], tmodels=[])) {
  if (Module m := t) {
    return checkModule(m, calculateDependencies(m, pcfg), pcfg, saveTModels = saveTModels);
  }
}
  
bool runRebelTests()
  = runTests([|project://rebel2/src/rebel/lang/tests/tests.ttl|], #Module, check);

TModel checkModule(loc spc) {
  PathConfig pfcg = pathConfig(srcs= [|project://rebel2/examples|], tmodels=[|project://rebel2/bin/tm|]);
  return check(parseModule(spc), saveTModels = true, pcfg = pfcg);
}
