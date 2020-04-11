module rebel::checker::Rebel2Alle

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;
 
import rebel::checker::translation::RelationsTranslator;
import rebel::checker::translation::ConstraintsTranslator;
import rebel::checker::translation::EventTranslator;
import rebel::checker::translation::FormulaAndExpressionTranslator;
import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::translation::ConfigTranslator;
import rebel::checker::translation::SyncedEventGraphBuilder;
import rebel::checker::translation::RelationCollector;
import rebel::checker::translation::ConfigAbstractionNormalizer;
import rebel::checker::RebelTrace;
import rebel::checker::Normalizer;
 
import util::PathUtil;

import ModelFinder;              // From AlleAlle
import translation::Syntax;      // From AlleAlle
import translation::AST;         // From AlleAlle
import translation::SMTInterface;// From AlleAlle
import ide::Parser;              // From AlleAlle
import ide::Imploder;            // From AlleAlle
import util::ModelPrinter;       // From AlleAlle
import smtlogic::Core;           // From AlleAlle
import smtlogic::Ints;           // From AlleAlle
import smtlogic::Strings;        // From AlleAlle

import IO;  
import ValueIO;
import Set;
import String;
import util::Maybe;
import util::Benchmark;

AlleAlleSnippet emptySnippet() = <{}, {}, {}, {}, (), {}, ()>;
AlleAlleSnippet merge(AlleAlleSnippet new, AlleAlleSnippet mergeTo) {
  mergeTo.typeCons += new.typeCons;
  mergeTo.fieldMultiplicityCons += new.fieldMultiplicityCons;
  mergeTo.paramMultiplicityCons += new.paramMultiplicityCons;
  mergeTo.eventPred += new.eventPred;
  mergeTo.transPred += new.transPred;
  mergeTo.facts += new.facts;
  mergeTo.asserts += new.asserts;
    
  return mergeTo;
}

Trace performCheck(Check chk, Module m, PathConfig pcfg, PathConfig normPcfg) = performCheck("<chk.name>", m, pcfg, normPcfg);

Trace performCheck(str check, Module m, PathConfig pcfg, PathConfig normPcfg) {
  Graph[RebelDependency] deps = calculateDependencies(m, pcfg);
  
  NormalizedResult nr  = loadNormalizedModules(m, pcfg, normPcfg);
  
  set[Module] allMods = {m | /Module m := nr.normDepGraph}; 
  list[RebelDependency] todo = order(nr.normDepGraph);
  
  AlleAlleSnippet allSnippets = emptySnippet();
  
  while (todo != []) {
    RebelDependency cur = todo[0];
    todo -= cur;
    
    Maybe[loc] mCurSnipFile = loadSnippet(cur.m);
    if (nothing() := mCurSnipFile || (just(loc curSnipFile) := mCurSnipFile && lastModified(curSnipFile) < cur.timestamp)) {
      println("Constructing allealle snippets for `<cur.m.\module.name>`");
      // No snippet made yet, or snippet belongs to earlier normalized module. Start new snippet creation
      AlleAlleSnippet snip = translateSnippet(cur.m, cur.tm, allMods); 
      writeTextValueFile(cur.m@\loc.top[extension="snip"], snip);
      
      allSnippets = merge(snip, allSnippets);
    } else if (just(loc curSnipFile) := mCurSnipFile) {
      AlleAlleSnippet snip = readTextValueFile(#AlleAlleSnippet, curSnipFile);
      allSnippets = merge(snip, allSnippets);
    }  
  }    
  
  //allMods = filterAbstractions(check, allMods, nr.normTm, nr.normDepGraph);
  
  Config cfg = buildConfig(check, allMods, nr.normTm);
  str alleSpec = translateSpecs(cfg, check, allMods, allSnippets);
   
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec), timeOutInMs = 30 * 1000);

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    stop();

    set[Module] mods = {m | /Module m := deps};
    
    Spec findSpec(Spec normSpec) = s when /Spec s := mods, "<s.name>" == "<normSpec.name>"; 
    rel[Spec spc, str instance] instances = {<findSpec(ns),inst> | <ns,inst> <- cfg.instances<0,1>}; 

    Trace trace = buildTrace(currentModel, mods, instances, cfg.finiteTrace);
    //Trace trace = buildTrace(currentModel, allMods, cfg.instances<0,1>, nr.normTm, cfg.finiteTrace);
    println(trace2Str(trace));
    
    return trace;
  } else if (timeout() := mfr) {
    return noTrace(solverTimeout());
  } else if (unsat(_) := mfr) {
    return noTrace(noSolutionFound());
  }
}

void translateSnippets(Module normalizedMod, Graph[RebelDependency] normDepGraph, PathConfig normPcfg) {
  if (/unresolvedModule(_) := normDepGraph) {
    throw "Unable to generate AlleAlle snippets for `<normalizedMod.\module.name>`. Some dependencies can not be resolved";
  }

  if (/resolvedOnlyModule(_,_) := normDepGraph) {
    throw "Unable to generate AlleAlle snippets for `<normalizedMod.\module.name>`. Not all normalized modules have been type checked";
  }     
  
  list[RebelDependency] todo = order(normDepGraph);
  set[Module] allMods = {m | /Module m := normDepGraph}; 
  
  while (todo != []) {
    RebelDependency cur = todo[0];
    todo -= cur;
    
    Maybe[loc] mCurSnipFile = loadSnippet(cur.m);
    if (nothing() := mCurSnipFile || (just(loc curSnipFile) := mCurSnipFile && lastModified(curSnipFile) < cur.timestamp)) {
      println("Constructing allealle snippets for `<cur.m.\module.name>`");
      // No snippet made yet, or snippet belongs to earlier normalized module. Start new snippet creation
      AlleAlleSnippet snip = translateSnippet(cur.m, cur.tm, allMods); 
      
      writeTextValueFile(cur.m@\loc.top[extension="snip"], snip);
    }  
  }  
}

private Maybe[loc] loadSnippet(Module m) {
  if (exists(m@\loc.top[extension = "snip"])) {
    return just(m@\loc.top[extension = "snip"]);
  } else {
    return nothing();
  }
}

private AlleAlleSnippet translateSnippet(Module normMod, TModel normTm, set[Module] allMods) {
  RelMapping rm = constructRelMapping(normMod, normTm, allMods);
  
  set[Spec] spcsToTrans = {s | /Spec s <- normMod.parts};
  set[Spec] allSpecs = {s | Module m <- allMods, /Spec s <- m.parts};
  
  rel[str,str] typeCons = machineFieldTypeConstraints(spcsToTrans, normTm);
  tuple[rel[str,str] typeCons, rel[str,str] multCons] paramCons = eventParamTypeAndMultiplicityConstraints(spcsToTrans, normTm); 
  
  return < machineFieldTypeConstraints(spcsToTrans, normTm) + paramCons.typeCons, //map[str,str] typeCons, 
           machineOnlyHasValuesWhenInitialized(spcsToTrans, normTm), //map[str,str] fieldMultiplicityCons, 
           paramCons.multCons, //map[str,str] paramMultiplicityCons,  
           translateEventsToPreds(spcsToTrans, rm, normTm, allSpecs), //map[str,str] eventPred, 
           constructTransitionFunctions(spcsToTrans, rm, normTm, allSpecs), //map[str,str] transPred, 
           translateFacts(normMod, rm, normTm, allSpecs), //map[str,str] facts, 
           translateAsserts(normMod, rm, normTm, allSpecs) //map[str,str] asserts, 
           >;  
}

rel[str,str] machineFieldTypeConstraints(set[Spec] spcs, TModel tm) {
  rel[str,str] typeCons = {};
  
  for (Spec spc <- spcs, /Field f <- spc.fields) {    
    if (isPrim(f.tipe, tm)) {
      typeCons["<spc.name>"] = "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>[config,instance]  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance]";
    } else {
      typeCons["<spc.name>"] = "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] ⨯ (Instance ⨝ <getSpecOfType(f.tipe, tm)>)[instance-\><f.name>]";
    }
  } 
  
  return typeCons;  
}
       
rel[str,str] machineOnlyHasValuesWhenInitialized(set[Spec] spcs, TModel tm) {
  rel[str,str] cons = {};
  
  for (Spec s <- spcs, /Field f <- s.fields) {    
    str relName = "<getCapitalizedSpecName(s)><getCapitalizedFieldName(f)>";
    
    if (isPrim(f.tipe, tm)) {
      cons["<s.name>"] = "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇔ one <relName> ⨝ c ⨝ inst)"; 
    } else {
      cons["<s.name>"] = "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (no (((c ⨯ inst) ⨝ instanceInState)[state] ∩ initialized) ⇒ no <relName> ⨝ c ⨝ inst)";  

      if (setType(_) !:= getType(f, tm) && optionalType(_) !:= getType(f, tm)) {
        cons["<s.name>"] = "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇒ one <relName> ⨝ c ⨝ inst)";  
      }
    }
  } 

  return cons;  
}

tuple[rel[str,str] typeCons, rel[str,str] multCons] eventParamTypeAndMultiplicityConstraints(set[Spec] spcs, TModel tm) {
  rel[str,str] typeCons = {};
  rel[str,str] multCons = {};

  for (Spec spc <- spcs, Event ev <- spc.events, /FormalParam p <- ev.params) {
    str relName = "ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>";

    if (isPrim(p.tipe, tm)) {
      typeCons["<spc.name>"] = "<relName>[cur,nxt] ⊆ order ∪ loop";
      multCons["<spc.name>"] = "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ one (step ⨝ <relName>))"; 
    } else {
      typeCons["<spc.name>"] = "<relName> ⊆ (order ∪ loop) ⨯ (Instance ⨝ <p.tipe.tp>)[instance-\><p.name>]";

      str mult = (setType(_) := getType(p, tm)) ? "some" : "one";
      multCons["<spc.name>"] = "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ <mult> (step ⨝ <relName>))";                 
    }
  }

  return <typeCons, multCons>;
}
   
rel[str,str] translateFacts(Module m, RelMapping rm, TModel tm, set[Spec] allSpecs) {
  int lastUnique = 0;
  int nxtUnique() { lastUnique += 1; return lastUnique; }
  Context ctx = ctx(rm, tm, allSpecs, defaultCurRel(), defaultStepRel(), nxtUnique);

  return {<"<s.name>", translate(f.form, ctx)> | /Spec s <- m.parts, Fact f <- s.facts};
}

map[str,str] translateAsserts(Module m, RelMapping rm, TModel tm, set[Spec] allSpecs) {
  int lastUnique = 0;
  int nxtUnique() { lastUnique += 1; return lastUnique; }
  Context ctx = ctx(rm, tm, allSpecs, defaultCurRel(), defaultStepRel(), nxtUnique);
  
  return ("<as.name>" : translate(as.form, ctx) | /Assert as <- m.parts);
}   

  
str translateSpecs(Config cfg, str check, set[Module] normalizedMods, AlleAlleSnippet allSnippets, bool debug = true) {
  set[Spec] normalizedSpecs = {inst.spc | inst <- cfg.instances};

  print("Translating Rebel to AlleAlle ...");
  
  int startTime = cpuTime();
  str alleSpec = "<translateRelationDefinitions(cfg)>
                 '<translateConstraints(cfg, allSnippets, normalizedSpecs)>
                 '<translateFacts(allSnippets)>
                 '<translateAssert(check, allSnippets)>
                 '// Minimize the number of steps by minimizing the number of Configurations
                 'objectives: minimize Config[count()]";
  
  println("done, took: <((cpuTime() - startTime) / 1000000)> ms.");
  if (debug) {
    writeFile(|project://rebel2/examples/latest-alle-spc.alle|, alleSpec);
  }
  
  return alleSpec;  
}  

str translateFacts(AlleAlleSnippet snippets) 
  = "<for (str spc <- snippets.facts<0>) {>// Fact from `<spc>`
    '<for (str fact <- snippets.facts[spc]) {><fact>
    '<}><}>";

str translateAssert(str check, AlleAlleSnippet snippets) {
  for (str name <- snippets.asserts, name == check) {
    return "// Assert `<name>`
           '<snippets.asserts[name]>";
  }
  
  throw "Unable to find assert with name `<check>`";
}
 