module analysis::allealle::tests::RelationCollectorTester

import analysis::allealle::RelationCollector;
import analysis::Normalizer;

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;

import util::PathUtil;

RelMapping analyse(loc rebelFile) {
  Module orig = parseModule(rebelFile);
  
  loc normRebelFile = normalize(orig, rebelTModelFromTree(orig, pathConf = pathConfig(src=[extractBase(orig)])));
  
  Module normalizedMod = parseModule(normRebelFile);
  return constructRelMapping({normalizedMod}, rebelTModelFromTree(normalizedMod, pathConf = pathConfig(src=[project(rebelFile) + "/bin/normalized"])));      
}