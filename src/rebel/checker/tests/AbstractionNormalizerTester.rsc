module rebel::checker::tests::AbstractionNormalizerTester

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::translation::ConfigAbstractionNormalizer;
import rebel::checker::Normalizer;

import util::PathUtil;

import IO;

void testTransaction() = testAbstractionNormalizer(|project://rebel2/examples/local/paper/Transaction.rebel|, "MockTrans");

void testAbstractionNormalizer(loc rebelMod, str config) {
  Module m = parseModule(rebelMod);
  
  PathConfig pcfg = defaultPathConfig(rebelMod);
  PathConfig normPcfg = normalizerPathConfig(rebelMod);
  
  Graph[RebelDependency] deps = calculateDependencies(m, pcfg);  
  NormalizedResult nr  = loadNormalizedModules(m, pcfg, normPcfg);

  set[Module] allMods = {m | /Module m := nr.normDepGraph}; 
  
  ar = filterAbstractions(config, allMods, nr.normTm, nr.normDepGraph);
  
}
