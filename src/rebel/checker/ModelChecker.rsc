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

import util::Benchmark;

alias ModelCheckerResult = tuple[Trace t, int checkAssemblyDuration, int normDuration, int configBuildDuration, int translateToAlleDuration, int translateToSmtDuration, int solveSolverDuration, int solveTotal, int constructRelModelDuration, int observedTotalDuration, int nrOfSmtVars, int nrOfSmtClauses];

ModelCheckerResult performCheck(Check chk, Module m, TModel tm, Graph[RebelDependency] deps, PathConfig pcfg = defaultPathConfig(m@\loc.top), bool saveIntermediateFiles = true, int solverTimeout = 30 * 1000, bool countNrOfVars = false, bool countNrOfClauses = false) {
  int startTime = realTime();

  // Step 1: Construct a new module containing all the Specifications that are refereced in the Config part of the check. 
  //         Also replace the abstracted specifications with the concrete mocks
  CheckedModule gen = assembleCheck(chk, m, tm, deps, pcfg, saveGenModule = saveIntermediateFiles);
  // Step 2: Normalize this combined, check specific Module 
  NormalizedModule norm = normalizeAndTypeCheck(gen.m, gen.tm, pcfg, saveNormalizedMod = saveIntermediateFiles); 
  // Step 3: Build a configuration containing all instances and initial values, etc.
  tuple[int,bool] steps = findSearchDepth(chk.depth);
  ConfigBuilderResult cfgRes = buildConfig(findConfigByName("<chk.config>",norm.m), norm.m, norm.tm, steps<0>, steps<1>, /(Objective)`infinite trace` := chk);

  // Step 4: Translate the normalized, combined module to an AlleAlle specification
  TransResult transRes = translateToAlleAlle(cfgRes.cfg, norm.m, norm.tm, pcfg, saveAlleAlleFile = saveIntermediateFiles);
  // Step 5: Run the translated AlleAlle specification in the ModelFinder and interpet the result (based on the generated, non-normalized, module)
  tuple[Trace t, int transToSmtDuration, int solveDuration, int solverTotal, int constructRelModelDuration, int nrOfVars, int nrOfClauses] modelFindRes = runAlleAlle(transRes.alleSpec, cfgRes.cfg, gen.m, solverTimeout, countNrOfVars, countNrOfClauses, saveSmtToFile = saveIntermediateFiles);
  
  int observedDuration = realTime() - startTime;
  
  return <modelFindRes.t, gen.duration , norm.duration, cfgRes.duration, transRes.duration, modelFindRes.transToSmtDuration, modelFindRes.solveDuration, modelFindRes.solverTotal, modelFindRes.constructRelModelDuration, observedDuration, modelFindRes.nrOfVars, modelFindRes.nrOfClauses>;
}

private tuple[Trace t, int transToSmtDuration, int solveDuration, int solverTotal, int constructRelModelDuration, int nrOfVars, int nrOfClauses] runAlleAlle(str alleSpec, Config cfg, Module m, int solverTimeOut, bool countNrOfVars, bool countNrOfClauses, bool saveSmtToFile = false) {  
  Spec findSpec(Spec spc) = s when /Spec s <- m.parts, "<s.name>" == "<spc.name>"; 

  Trace extractTrace(Model model) {
    rel[Spec spc, str instance] instances = {<findSpec(ns),inst> | <ns,inst> <- cfg.instances<0,1>}; 
    Trace trace = buildTrace(model, {m}, instances, cfg.finiteTrace);
    return trace;
  }
 
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec), timeOutInMs = solverTimeOut, countNrOfVars = countNrOfVars, countNrOfClauses = countNrOfClauses, saveSMTToFile=saveSmtToFile);
 
  switch(mfr) {
    case sat(Model currentModel, Model (Domain) nextModel, void () stop): {
      stop();
      
      Trace t = extractTrace(currentModel);
      return <t, mfr.translationTime, mfr.solvingTimeSolver, mfr.solvingTimeTotal, mfr.constructModelTime, mfr.nrOfVars, mfr.nrOfClauses>;
    } 
    case trivialSat(Model model): return <extractTrace(model), mfr.translationTime, mfr.solvingTimeSolver, mfr.solvingTimeTotal, mfr.constructModelTime, mfr.nrOfVars, mfr.nrOfClauses>;

    case unsat(_): return <noTrace(noSolutionFound()), mfr.translationTime, mfr.solvingTimeSolver, mfr.solvingTimeTotal, mfr.constructModelTime, mfr.nrOfVars, mfr.nrOfClauses>;
    case trivialUnsat(): return <noTrace(noSolutionFound()), mfr.translationTime, mfr.solvingTimeSolver, mfr.solvingTimeTotal, mfr.constructModelTime, mfr.nrOfVars, mfr.nrOfClauses>;

    case timeout(): return <noTrace(solverTimeout()), mfr.translationTime, mfr.solvingTimeSolver, mfr.solvingTimeTotal, mfr.constructModelTime, mfr.nrOfVars, mfr.nrOfClauses>;

    default: throw "Unable to handle response from model finder"; 
  }
}

private rebel::lang::Syntax::Config findConfigByName(str cfgName, Module m) {
  for (/rebel::lang::Syntax::Config cfg <- m.parts, "<cfg.name>" == cfgName) {
    return cfg;
  } 
  
  throw "Unable to find referenced Config at `<chk.config@\loc>`";
}

private tuple[int,bool] findSearchDepth((SearchDepth)`max <Int steps> steps`) = <toInt("<steps>") + 1, false>;
private tuple[int,bool] findSearchDepth((SearchDepth)`exact <Int steps> steps`) = <toInt("<steps>") + 1, true>;