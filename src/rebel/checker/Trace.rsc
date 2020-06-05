module rebel::checker::Trace
 
import rebel::lang::Syntax; 
//import rebel::lang::Parser;
//import rebel::lang::TypeChecker;

import rebel::checker::translation::CommonTranslationFunctions;

import translation::SMTInterface;// From AlleAlle
import util::ModelPrinter;       // From AlleAlle
import smtlogic::Core;           // From AlleAlle
import smtlogic::Ints;           // From AlleAlle
import smtlogic::Strings;        // From AlleAlle

import IO;   
import Set;
import String; 
import List;

data Trace
  = step(Configuration conf, RaisedEvent re, Trace next)
  | goal(Configuration conf)
  | goalInfiniteTrace(Configuration conf, RaisedEvent re, int backTo)
  | noTrace(Reason reason)
  ;

data Reason
  = solverTimeout()
  | noSolutionFound()
  ;

data Configuration 
  = config(rel[Spec spc, str instance, State state] instances, rel[Spec spc, str instance, str field, str val] values)
  ;

data RaisedEvent
  = raisedEvent(Spec spc, Event event, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
  | raisedEventVariant(Spec spc, Event event, str eventName, str variant, str instance, rel[str param, str val] arguments, set[str] affectedInstances)
  ;

Trace buildTrace(Model alleModel, set[Module] mods, rel[Spec spc, str instance] instances, bool finiteTrace) {
  set[Spec] specs = {s | Module m <- mods, /Spec s <- m.parts};
  
  int nrOfConfigs = getNrOfConfigs(alleModel); 

  Trace buildTrace(int stepNr) = step(getConfiguration(stepNr, specs, instances, alleModel), getRaisedEvent(stepNr, specs, instances, alleModel), buildTrace(stepNr + 1)) when stepNr < nrOfConfigs;
  default Trace buildTrace(int stepNr) = goal(getConfiguration(stepNr, specs, instances, alleModel)) when finiteTrace;
  default Trace buildTrace(int stepNr) = goalInfiniteTrace(getConfiguration(stepNr, specs, instances, alleModel), getRaisedEvent(stepNr, specs, instances, alleModel), getBackTo(alleModel)) when !finiteTrace; 

  return buildTrace(1);   
}

int getNrOfConfigs(Model alleModel) {
  configRel = findRelation(alleModel, "Config");
  configRel.tuples = sort(configRel.tuples, bool (ModelTuple a, ModelTuple b) { return getNumber(a, "c") < getNumber(b, "c");});  
  
  int nrOfConfigs = getNumber(configRel.tuples[-1], "c");
  return nrOfConfigs;
}

int getBackTo(Model alleModel) { 
  loopRel = findRelation(alleModel, "loop");
  
  if (/idAttribute("nxt", str id) := loopRel.tuples[0]) {
    return getNumber(id, "c");
  }  
  
  throw "Unable to find configuration to link back to";
}

int getNumber(fixedTuple([idAttribute(str _, str id)]), str prefix) = getNumber(id, prefix);
int getNumber(varTuple([idAttribute(str _, str id)], str _), str prefix) = getNumber(id, prefix);

int getNumber(str idVal, str prefix) = toInt(replaceFirst(idVal, prefix, ""));

Configuration getConfiguration(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel) {
  rel[Spec,str,State] states = {};
  rel[Spec,str,str,str] values = {};
  
  for (s <- specs) {
    states += getStateInConfig(step, s, instances[s], alleModel);
    values += getValuesInConfig(step, s, instances[s], alleModel);
  }
  
  return config(states, values);
}

ModelRelation findRelation(Model m, str name) {
  str lcName = toLowerCase(name);
  
  for (r:mRelation(str relName,  _, list[ModelTuple] _) <- m.relations, toLowerCase(relName) == lcName) {
    return r;
  }
  
  throw "Unable to find relation with name `<name>` in found AlleAlle model";
}

rel[Spec spc, str instance, State state] getStateInConfig(int step, Spec spc, set[str] instances, Model alleModel) {
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

rel[Spec spc, str instance, str field, str val] getValuesInConfig(int step, Spec spc, set[str instance] instances, Model alleModel) {
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

RaisedEvent getRaisedEvent(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel) {
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
  
  Event findEvent(Spec spc, str eventName) = e 
    when /Event e := spc.events, 
         "<toLowerCase("<e.name>")>" == eventName;
  
  Event findEvent(Spec spc, "empty") = (Event)`event empty()`;
  
  default Event findEvent(Spec spc, str eventName) { 
    throw "Unable to find event `<eventName>`;"; 
  }

  str getValue(ModelRelation r, str param) {
    for (t <- r.tuples) {
      if (/idAttribute("cur", "c<step>") := t.attributes) {
        return findAssignedValue(t, param);
      }
    }
    
    throw "Unable to find value for param `<param>` in step <step>";
  }

  tuple[str event,str variant] parseEventName(str rawEvent, str spcName) {
    if (/^event_<s:.*>_<eventName:.*>__<variant:.*>$/ := rawEvent, s == spcName) {
      return <eventName, variant>;
    } else if (/^event_<s:.*>_<eventName:.*>$/ := rawEvent, s == spcName) {
      return <eventName, "">;
    } else {
      throw "Unable to parse event name `<rawEvent>`";
    }
  }

  tuple[str instance, str event] ie = findInstanceAndEvent();
      
  Spec spc = findSpec(ie.instance);
  tuple[str eventName, str variant] en = parseEventName(ie.event, toLowerCase("<spc.name>"));
  str getAlleEventName() = en.variant != "" ? "<en.eventName>__<en.variant>" : en.eventName; 

  Event ev = findEvent(spc, en.eventName);

  rel[str param, str val] args = {};

  for (FormalParam p <- ev.params) {
    ModelRelation op = findRelation(alleModel, "ParamEvent<getCapitalizedSpecName(spc)><getAlleEventName()><getCapitalizedParamName(p)>");
    
    for (str val := getValue(op, "<p.name>")) {
      args += <"<p.name>", val>;
    } 
  }
  
  ModelRelation ai = findRelation(alleModel, "changedInstance");
  set[str] affectedInstances = {instance | t <- ai.tuples, /idAttribute("cur", "c<step>") := t.attributes, str instance := findAssignedValue(t, "instance")};

  if (en.variant != "") {
    return raisedEventVariant(spc, ev, en.eventName, en.variant, ie.instance, args, affectedInstances);  
  } else {
    return raisedEvent(spc, ev, ie.instance, args, affectedInstances);
  }
}

str trace2Str(Trace t) = 
  "
  'FOUND TRACE:
  '===============
  '<trace2Str(1, t)>";

str trace2Str(int step, step(Configuration cfg, RaisedEvent re, Trace next))
  = "Configuration <step>: 
    '---------------
    '<config2Str(cfg)>
    '<raisedEvent2Str(re)>
    '
    '<trace2Str(step+1, next)>";

str trace2Str(int step, goal(Configuration cfg)) 
  = "Configuration <step>: (GOAL)
    '---------------
    '<config2Str(cfg)>";

str trace2Str(int step, goalInfiniteTrace(Configuration cfg, RaisedEvent re, int backTo)) 
  = "Configuration <step>: (GOAL)
    '---------------
    '<config2Str(cfg)>
    '<raisedEvent2Str(re)>
    'Back to Configuration <backTo>";


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
    