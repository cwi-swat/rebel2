module rebel::checker::ModelChecker

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::Normalizer;
import rebel::checker::CheckAssembler;
import rebel::checker::ConfigTranslator;
import rebel::checker::RebelToAlleTranslator;
import rebel::checker::Trace;

import util::PathUtil;

import ModelFinder;              // From AlleAlle
import translation::AST;         // From AlleAlle
import translation::SMTInterface;// From AlleAlle
import ide::Imploder;            // From AlleAlle
import util::ModelPrinter;       // From AlleAlle

import ParseTree;
import String;
import IO;

Trace performCheck(Check chk, Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true) {
  CheckedModule gen = assembleCheck(chk, m, tm, deps, pcfg, saveGenModule = saveIntermediateFiles);
  CheckedModule norm = normalizeAndTypeCheck(gen.m, gen.tm, pcfg, saveNormalizedMod = saveIntermediateFiles); 
  
  Config cfg = buildConfig(findConfigByName("<chk.config>",norm.m), norm.m, norm.tm, findSearchDepth(chk.depth), /(Objective)`infinite trace` := chk);
  
  str alleSpec = translateToAlleAlle(cfg, norm.m, norm.tm, pcfg, saveAlleAlleFile = saveIntermediateFiles);
  
  return runAlleAlle(alleSpec, cfg, gen.m); 
}

private Trace runAlleAlle(str alleSpec, Config cfg, Module m, int solverTimeOut = 30 * 1000) {
  Spec findSpec(Spec spc) = s when /Spec s <- m.parts, "<s.name>" == "<spc.name>"; 

  Trace extractTrace(Model model) {
    rel[Spec spc, str instance] instances = {<findSpec(ns),inst> | <ns,inst> <- cfg.instances<0,1>}; 
    Trace trace = buildTrace(model, {m}, instances, cfg.finiteTrace);
    return trace;
  }
 
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec), timeOutInMs = solverTimeOut);
 
  switch(mfr) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): {
      stop();
      return extractTrace(currentModel);
    } 
    case trivialSat(Model model): return extractTrace(model);

    case unsat(_): return noTrace(noSolutionFound());
    case trivialUnsat(): return noTrace(noSolutionFound());

    case timeout(): return noTrace(solverTimeout());

    default: throw "Unable to handle response from model finder"; 
  }
}

private rebel::lang::Syntax::Config findConfigByName(str cfgName, Module m) {
  for (/rebel::lang::Syntax::Config cfg <- m.parts, "<cfg.name>" == cfgName) {
    return cfg;
  } 
  
  throw "Unable to find referenced Config at `<chk.config@\loc>`";
}

private int findSearchDepth((SearchDepth)`max <Int steps> steps`) = toInt("<steps>") + 1;