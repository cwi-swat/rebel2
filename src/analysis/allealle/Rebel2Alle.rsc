module analysis::allealle::Rebel2Alle

import rebel::lang::SpecSyntax;
import rebel::lang::SpecParser;
import rebel::lang::SpecTypeChecker;

import analysis::allealle::StaticRelationsTranslator;
import analysis::allealle::DynamicRelationsTranslator;
import analysis::allealle::ConstraintsTranslator;
import analysis::allealle::CommonTranslationFunctions;
import util::PathUtil;

import ide::CombinedModelFinder; // From AlleAlle
import ide::CombinedSyntax;      // From AlleAlle
import ide::Parser;              // From AlleAlle
import ide::CombinedAST;         // From AlleAlle
import ide::CombinedImploder;    // From AlleAlle
import util::ModelPrinter;       // From AlleAlle
import smtlogic::Core;              // From AlleAlle
import smtlogic::Ints;              // From AlleAlle
  
import IO;  
import Set;
import String;
import util::Maybe;
  
void translateSpecs(Config config, str check, bool debug = true) {
  set[Spec] normalizedSpecs = {inst.spc | inst <- config.instances};
  str alleSpec = "<translateStaticPart(normalizedSpecs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(normalizedSpecs, config, check)>";
  
  if (debug) {
    writeFile(project(getOneFrom(normalizedSpecs)@\loc.top) + "examples/latest-alle-spc.alle", alleSpec);
  }
  
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec));

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    stop();
    Trace trace = buildTrace(currentModel, normalizedSpecs, config.instances<0,1>, config.tm);
    println(trace2Str(trace));
  }
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

Trace buildTrace(Model alleModel, set[Spec] specs, rel[Spec spc, str instance] instances, TModel tm) {
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
  
  for (s <- specs) {
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

Maybe[str] findAssignedValue(ModelTuple t, str field) {
  str parseTerm(lit(Literal l)) = model2Str(l);
  str parseTerm(neg(Term t)) = "-<model2Str(t)>";
  str parseTerm(\int(int i)) = "<i>";

  if (/idAttribute(field, str id) := t.attributes) {
    return just(id);
  } else if (/fixedAttribute(field, Term val) := t.attributes) {
    return just(parseTerm(val));
  } else if (/varAttribute(field, Term val, _) := t.attributes) {
    return just(parseTerm(val));
  } else {
    return nothing();
  }
}

rel[Spec spc, str instance, str field, str val] getValuesInConfig(int step, Spec spc, set[str instance] instances, Model alleModel, TModel tm) {
  rel[Spec,str,str,str] values = {};
    
  Maybe[str] getValue(ModelRelation r, str inst, str field) {
    for (t <- r.tuples) {
      if (/idAttribute("config", "c<step>") := t.attributes && /idAttribute("instance", inst) := t.attributes) {
        return findAssignedValue(t, field);
      }
    }
    
    return nothing();
  }

  for (/Field f <- spc.fields) {
    ModelRelation r = findRelation(alleModel, "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>");
    for (inst <- instances, just(str val) := getValue(r, inst, "<f.name>")) {
      values += <spc, inst, "<f.name>", val>;
    }
  }
  return values;
}

RaisedEvent getRaisedEvent(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel, TModel tm) {
  ModelRelation r = findRelation(alleModel, "raisedEvent");

  tuple[str,str] findInstanceAndEvent() {
    for (t <- r.tuples, /idAttribute("cur", "c<step>") := t.attributes, just(str instance) := findAssignedValue(t, "instance"), just(str event) := findAssignedValue(t, "event")) {
      return <instance,event>;
    }
    
    throw "Unable to find raised event in step `<step>`";
  }
     
  Spec findSpec(str instance) = spc
    when /<Spec normalizedSpc, instance> := instances,
      Spec spc <- specs,
      "<spc.name>" == "<normalizedSpc.name>";
  
  Event findEvent(Spec spc, str eventName) = e when /Event e := spc.events, "<toLowerCase("<e.name>")>" == eventName;

  Maybe[str] getValue(ModelRelation r, str param) {
    for (t <- r.tuples) {
      if (/idAttribute("cur", "c<step>") := t.attributes) {
        return findAssignedValue(t, param);
      }
    }
    
    return nothing();
  }

  tuple[str instance, str event] ie = findInstanceAndEvent();   
  Spec spc = findSpec(ie.instance);
  Event ev = findEvent(spc, replaceAll(ie.event, "event_<toLowerCase("<spc.name>")>_", ""));

  rel[str param, str val] args = {};

  for (FormalParam p <- ev.params) {
    ModelRelation op = findRelation(alleModel, "ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>");
    
    for (just(str val) := getValue(op, "<p.name>")) {
      args += <"<p.name>", val>;
    } 
  }
  
  ModelRelation ai = findRelation(alleModel, "changedInstance");
  set[str] affectedInstances = {instance | t <- ai.tuples, /idAttribute("cur", "c<step>") := t.attributes, just(str instance) := findAssignedValue(t, "instance")};

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
private default str getVal(set[str] val) = val;

str config2Str(Configuration cfg) {
  str getState(uninitialized()) = "uninitialized";
  str getState(finalized()) = "finalized";
  str getState(state(str st)) = st;

  str result = "";
  for (Spec s <- cfg.instances<0>, str inst <- cfg.instances[s]<0>, State st <- cfg.instances[s,inst]) {
    result += "<inst> (<s.name>) in `<getState(st)>` : <intercalate(", ", ["<field> = <getVal(cfg.values[s,inst,field])>" | str field <- cfg.values[s,inst]<0>])>\n";  
  }
  return result;
}

private str getRaisedEventName(RaisedEvent re) = "<re.event.name>" when !(re has eventName); 
private str getRaisedEventName(RaisedEvent re) = "<re.eventName>" when (re has eventName);

str raisedEvent2Str(RaisedEvent re) 
  = "--\> Raised <getRaisedEventName(re)>(<args2Str(re.arguments)>)<if (re has variant) {> (variant `<re.variant>`)<}> on <re.instance> (<re.spc.name>) : affected instances {<intercalate(",", toList(re.affectedInstances))>}";
  
str args2Str(rel[str field, str val] args) 
  = intercalate(", ", ["<f> = <getVal(args[f])>" | str f <- args<0>]);
  