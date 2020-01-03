module rebel::lang::tests::DependencyAnalyzerTester

import rebel::lang::DependencyAnalyzer;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;

import util::PathUtil;
import util::Maybe;

import IO; 
import String;
import DateTime;
import Set;

Graph[RebelDependency] calc(loc modul) {
  PathConfig pcfg = pathConfig(srcs=[|project://rebel2/examples|], tmodels=[|project://rebel2/bin/tm|]);
  
  return calculateDependencies(parseModule(modul), pcfg);
}
