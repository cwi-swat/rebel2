module analysis::allealle::Rebel2Alle

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;

import analysis::allealle::StaticRelationsTranslator;
import analysis::allealle::DynamicRelationsTranslator;
import analysis::allealle::ConstraintsTranslator;
import analysis::allealle::CommonTranslationFunctions;
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
import Set;
import String;
import util::Maybe;
import util::Benchmark;

import analysis::allealle::Rebel2Alle;
import analysis::allealle::ConfigTranslator;
import analysis::allealle::LTLTranslator;
import analysis::allealle::SyncedEventGraphBuilder;

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;

import analysis::allealle::CommonTranslationFunctions;

import analysis::Normalizer;
import util::PathUtil;
import analysis::graphs::Graph;

void performCheck(Check chk, Module m, PathConfig pathConf = pathConfig(srcs=[extractBase(m)]))
  = performCheck("<chk.name>", m, pathConf = pathConf);

void performCheck(str check, Module m, PathConfig pathConf = pathConfig(srcs=[extractBase(m)])) {
  PathConfig normPathConfig = pathConfig(srcs=[project(m@\loc.top) + "/bin/normalized"]);
  
  tuple[Module initModule, set[Module] allMods] normalized = normalizeAllInScope(m, pathConf, normPathConfig);  
  TModel tm = rebelTModelFromTree(normalized.initModule, pathConf = normPathConfig);  
  
  Config cfg = buildConfig(check, normalized.allMods, tm);
  str alleSpec = translateSpecs(cfg, buildAssert(check, normalized.allMods, tm));
   
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec));

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    stop();
    Trace trace = buildTrace(currentModel, normalized.allMods, cfg.instances<0,1>, tm);
    println(trace2Str(trace));
  }  
}

private tuple[Module, set[Module]] normalizeAllInScope(Module startingPoint, PathConfig pcfg, PathConfig normalizedPcfg) {
  TModel origTm = rebelTModelFromTree(startingPoint, pathConf = pcfg);  
  
  set[QualifiedName] gatherImports(Module m) = {imp.\module | Import imp <- m.imports};
   
  set[Module] normalizedMods = {}; 
  set[QualifiedName] imported = {};
  set[QualifiedName] modulesToImport = gatherImports(startingPoint);
    
  while (set[QualifiedName] todo := modulesToImport, modulesToImport != {}) {
    modulesToImport = {};
    for (m <- todo, m notin imported) {
      
      if (just(loc l) := lookupModule(m, pcfg)) {
        Module n = parse(#start[Module], l).top;
        modulesToImport += gatherImports(n);
        normalizedMods += parse(#start[Module], normalize(n, origTm)).top;
      }
      else {
        throw "Cannot find module <m>";
      }
          
      imported += m; 
    }
  }
  
  Module normStartPoint = parse(#start[Module], normalize(startingPoint, origTm)).top;
  return <normStartPoint, normalizedMods + normStartPoint>;
}

private Maybe[loc] lookupModule(QualifiedName name, PathConfig pcfg) {
    for (s <- pcfg.srcs) {
        result = (s + replaceAll("<name>", "::", "/"))[extension = "rebel"];

        if (exists(result)) {
          return just(result);
        }
    }
    
    return nothing();
}
  
str translateSpecs(Config config, str check, bool debug = true) {
  set[Spec] normalizedSpecs = {inst.spc | inst <- config.instances};

  print("Translating Rebel to AlleAlle ...");
  tuple[str alleSpec, int time] res = bmTranslate(normalizedSpecs, config, check);
  println("done, took: <res.time> ms.");
  
  if (debug) {
    writeFile(project(getOneFrom(normalizedSpecs)@\loc.top) + "examples/latest-alle-spc.alle", res.alleSpec);
  }
  
  return res.alleSpec;  
}  

private tuple[str, int] bmTranslate(set[Spec] normalizedSpecs, Config cfg, str check) {
  int startTime = cpuTime();

  str alleSpec = "<translateStaticPart(normalizedSpecs)>
                 '<translateDynamicPart(cfg)>
                 '<translateConstraints(normalizedSpecs, cfg, check)>";

  return <alleSpec, (cpuTime() - startTime) / 1000000>;
}


data Trace
  = step(Configuration conf, RaisedEvent re, Trace next)
  | goal(Configuration conf)
  ;

data Configuration 
  = config(rel[Spec spc, str instance, State state] instances, rel[Spec spc, str instance, str field, str val] values)
  ;

data RaisedEvent
  = raisedEvent(Spec spc, Event event, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
  | raisedEventVariant(Spec spc, Event event, str eventName, str variant, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
  ;

Trace buildTrace(Model alleModel, set[Module] mods, rel[Spec spc, str instance] instances, TModel tm) {
  set[Spec] specs = {s | Module m <- mods, /Spec s <- m.parts};
  
  int nrOfConfigs = getNrOfConfigs(alleModel); 

  Trace buildTrace(int stepNr) = step(getConfiguration(stepNr, specs, instances, alleModel, tm), getRaisedEvent(stepNr, specs, instances, alleModel, tm), buildTrace(stepNr + 1)) when stepNr < nrOfConfigs;
  default Trace buildTrace(int stepNr) = goal(getConfiguration(stepNr, specs, instances, alleModel, tm)); 

  return buildTrace(1);   
}

int getNrOfConfigs(Model alleModel) {
  configRel = findRelation(alleModel, "Config");
  configRel.tuples = sort(configRel.tuples, bool (ModelTuple a, ModelTuple b) { return getNumber(a, "c") < getNumber(b, "c");});  
  
  int nrOfConfigs = getNumber(configRel.tuples[-1], "c");
  return nrOfConfigs;
}

int getNumber(fixedTuple([idAttribute(str _, str id)]), str prefix) = getNumber(id, prefix);
int getNumber(varTuple([idAttribute(str _, str id)], str _), str prefix) = getNumber(id, prefix);

int getNumber(str idVal, str prefix) = toInt(replaceFirst(idVal, prefix, ""));

Configuration getConfiguration(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel, TModel tm) {
  rel[Spec,str,State] states = {};
  rel[Spec,str,str,str] values = {};
  
  for (s <- specs, !isEmptySpec(s)) {
    states += getStateInConfig(step, s, instances[s], alleModel, tm);
    values += getValuesInConfig(step, s, instances[s], alleModel, tm);
  }
  
  return config(states, values);
}

ModelRelation findRelation(Model m, str name) {
  for (r:mRelation(name,  _, list[ModelTuple] _) <- m.relations) {
    return r;
  }
  
  throw "Unable to find relation with name `<name>` in found AlleAlle model";
}

rel[Spec spc, str instance, State state] getStateInConfig(int step, Spec spc, set[str] instances, Model alleModel, TModel tm) {
  rel[Spec,str,State] instanceStates = {};
  
  ModelRelation r = findRelation(alleModel, "instanceInState");

  State getState(str inst) {
    if (isEmptySpec(spc)) {
      return noState();
    }
    
    for (t <- r.tuples) {
      if (/idAttribute("config", "c<step>") := t.attributes && /idAttribute("instance", inst) := t.attributes, /idAttribute("state", str curState) := t.attributes) {
        return parseState(curState);
      }
    }
    
    throw "Unable to find state for `<inst>` in step `<step>`";
  }
  
  State parseState("state_uninitialized") = uninitialized();
  State parseState("state_finalized") = finalized();
  default State parseState(str st) = state(substring(st, findLast(st, "_")+1));

  for (inst <- instances) {
    instanceStates += {<spc, inst, getState(inst)>};
  }
  
  return instanceStates;
}

str findAssignedValue(ModelTuple t, str field) {
  str parseTerm(lit(Literal l)) = model2Str(l);
  str parseTerm(neg(Term t)) = "-<model2Str(t)>";
  str parseTerm(\int(int i)) = "<i>";

  if (/idAttribute(field, str id) := t.attributes) {
    return id;
  } else if (/fixedAttribute(field, Term val) := t.attributes) {
    return parseTerm(val);
  } else if (/varAttribute(field, Term val, _) := t.attributes) {
    return parseTerm(val);
  } else {
    throw "Unable to parse value for field `<field>` in tuples `<t>`";
  }
}

rel[Spec spc, str instance, str field, str val] getValuesInConfig(int step, Spec spc, set[str instance] instances, Model alleModel, TModel tm) {
  rel[Spec,str,str,str] values = {};
    
  list[str] getValues(ModelRelation r, str inst, str field) {
    list[str] foundValues = [];
    
    for (t <- r.tuples) {
      if (/idAttribute("config", "c<step>") := t.attributes && /idAttribute("instance", inst) := t.attributes) {
        foundValues += findAssignedValue(t, field);
      }
    }

    return foundValues;
  }

  for (/Field f <- spc.fields) {
    ModelRelation r = findRelation(alleModel, "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>");
    for (inst <- instances, str val <- getValues(r, inst, "<f.name>")) {
      values += <spc, inst, "<f.name>", val>;
    }
  }
  return values;
}

RaisedEvent getRaisedEvent(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel, TModel tm) {
  ModelRelation r = findRelation(alleModel, "raisedEvent");

  tuple[str,str] findInstanceAndEvent() {
    for (t <- r.tuples, /idAttribute("cur", "c<step>") := t.attributes, str instance := findAssignedValue(t, "instance"), str event := findAssignedValue(t, "event")) {
      return <instance,event>;
    }
    
    throw "Unable to find raised event in step `<step>`";
  }
     
  Spec findSpec(str instance) = spc
    when /<Spec normalizedSpc, instance> := instances,
      Spec spc <- specs,
      "<spc.name>" == "<normalizedSpc.name>";
  
  Event findEvent(Spec spc, str eventName) = e when /Event e := spc.events, "<toLowerCase("<e.name>")>" == eventName;

  str getValue(ModelRelation r, str param) {
    for (t <- r.tuples) {
      if (/idAttribute("cur", "c<step>") := t.attributes) {
        return findAssignedValue(t, param);
      }
    }
    
    throw "Unable to find value for param `<param>` in step <step>";
  }

  tuple[str instance, str event] ie = findInstanceAndEvent();   
  Spec spc = findSpec(ie.instance);
  Event ev = findEvent(spc, replaceAll(ie.event, "event_<toLowerCase("<spc.name>")>_", ""));

  rel[str param, str val] args = {};

  for (FormalParam p <- ev.params) {
    ModelRelation op = findRelation(alleModel, "ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>");
    
    for (str val := getValue(op, "<p.name>")) {
      args += <"<p.name>", val>;
    } 
  }
  
  ModelRelation ai = findRelation(alleModel, "changedInstance");
  set[str] affectedInstances = {instance | t <- ai.tuples, /idAttribute("cur", "c<step>") := t.attributes, str instance := findAssignedValue(t, "instance")};

  if (/^<evName:.*>__<varName:.*>$/ := "<ev.name>") {
    return raisedEventVariant(spc, ev, evName, varName, ie.instance, args, affectedInstances);  
  } else {
    return raisedEvent(spc, ev, ie.instance, args, affectedInstances);
  }
}

str trace2Str(Trace t) = 
  "
  'FOUND TRACE:
  '===============
  '<trace2Str(1, t)>";

str trace2Str(int step, step(Configuration cfg, RaisedEvent re, Trace next)) =
  "Configuration <step>: 
  '---------------
  '<config2Str(cfg)>
  '<raisedEvent2Str(re)>
  '
  '<trace2Str(step+1, next)>";

str trace2Str(int step, goal(Configuration cfg)) 
  = "Configuration <step>: (GOAL)
    '<config2Str(cfg)>";

private str getVal({str v}) = v;
private default str getVal(set[str] val) = "{<intercalate(",", [*val])>}";

str config2Str(Configuration cfg) {
  str getState(uninitialized()) = "is `uninitialized`";
  str getState(finalized()) = "is `finalized`";
  str getState(state(str st)) = "is `<st>`";
  str getState(noState()) = "";

  str result = "";
  for (Spec s <- cfg.instances<0>, str inst <- cfg.instances[s]<0>, State st <- cfg.instances[s,inst]) {
    result += "<inst> (<s.name>) <getState(st)> : <intercalate(", ", ["<field> = <getVal(cfg.values[s,inst,field])>" | str field <- cfg.values[s,inst]<0>])>\n";  
  }
  return result;
}

private str getRaisedEventName(RaisedEvent re) = "<re.event.name>" when !(re has eventName); 
private str getRaisedEventName(RaisedEvent re) = "<re.eventName>" when (re has eventName);

str raisedEvent2Str(RaisedEvent re) 
  = "--\> Raised <getRaisedEventName(re)>(<args2Str(re.arguments)>)<if (re has variant) {> (variant `<re.variant>`)<}> on <re.instance> (<re.spc.name>) : affected instances {<intercalate(",", toList(re.affectedInstances))>}";
  
str args2Str(rel[str field, str val] args) 
  = intercalate(", ", ["<f> = <getVal(args[f])>" | str f <- args<0>]);
  