module rebel::checker::translation::RelationsTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import rebel::checker::ConfigTranslator;
import rebel::checker::translation::CommonTranslationFunctions;

import String;
import Set;
import List;

str translateRelationDefinitions(Config cfg, TModel tm) 
  = "<translateStaticPart(cfg.instances<0>)>
    '
    '<translateDynamicPart(cfg, tm)>
    ";

private str translateStaticPart(set[Spec] spcs) {
  str def = "// Static configuration of state machines
            '<buildSpecRel(spcs)>
            '<buildStateRel(spcs)>
            '<buildAllowedTransitionRel(spcs)>
            '<buildEventsAsSingleRels(spcs)>
            '<buildConstantRels(spcs)>"; 

  return def;
}

private str translateDynamicPart(Config cfg, TModel tm) {
  str def = "// Dynamic configuration of state machines
            '<buildConfigRels(cfg.numberOfTransitions, cfg.finiteTrace, cfg.exactNrOfSteps)>
            '<buildInstanceRel(cfg.instances)>
            '<buildInstanceInStateRel(cfg.instances, cfg.numberOfTransitions)>
            '<buildRaisedEventsRel(cfg.instances<0,1>, cfg.numberOfTransitions, cfg.finiteTrace)>
            '<buildChangedInstancesRel(cfg.instances<0,1>, cfg.numberOfTransitions, cfg.finiteTrace)>
            '<buildStateVectors(lookupSpecs(cfg.instances), cfg, tm)>
            '<buildEnumRels(lookupSpecs(cfg.instances))>
            '<buildEventParamRels(lookupSpecs(cfg.instances), cfg, tm)>"; 

  return def;
}


private str buildSpecRel(set[Spec] spcs) 
  = "// Define the specs that can take place in the transition system
    '<for (s <- spcs) {><buildSpecRel(s)>
    '<}>";
  
private str buildSpecRel(Spec spc) 
  = "<getCapitalizedSpecName(spc)> (spec:id) = {\<<getLowerCaseSpecName(spc)>\>}";  
  
private str buildStateRel(set[Spec] spcs) 
  = "// Define all possible states for all machines
    'State (state:id) = {\<state_uninitialized\>,\<state_finalized\><if (stateTuples != "") {>,<stateTuples><}>}
    'initialized (state:id) = {<stateTuples>}
    'finalized (state:id) = {\<state_finalized\>}
    'uninitialized (state:id) = {\<state_uninitialized\>}
    '<buildIndividualStateRels(spcs)>"
  when stateTuples := intercalate(",", [st | s <- spcs, str st := buildStateTuples(s), st != ""]);

private str buildIndividualStateRels(set[Spec] spcs)
  = "<for (s <- spcs) {><buildIndividualStateRel(s)>
    '<}>";

private str buildIndividualStateRel(Spec spc)
  = "<for (rebel::lang::SpecSyntax::State s <- states) {>State<getCapitalizedSpecName(spc)><capitalize(replaceAll("<s>", "::", "__"))> (state:id) = {\<<getStateLabel(spc, s)>\>}
    '<}>"
    when set[rebel::lang::SpecSyntax::State] states := lookupStates(spc);
  
private str buildStateTuples(Spec spc) 
  = intercalate(",", ["\<state_<s>\>" | str s <- states])
  when 
    str name := getLowerCaseSpecName(spc),
    set[str] states := {"<name>_<toLowerCase(replaceAll("<s.name>", "::", "__"))>" | /rebel::lang::SpecSyntax::State s := spc.states, s has name};

private str buildAllowedTransitionRel(set[Spec] spcs)
  = "// Define which transitions are allowed (in the form of `from a state` -\> ` via an event` -\> `to a state`
    'allowedTransitions (from:id, to:id, event:id) = {<intercalate(",", [tt | s <- spcs, str tt := buildAllowedTransitionTuples(s), tt != ""])>}";

private str buildAllowedTransitionTuples(Spec spc)
  = intercalate(",", ["\<<f>,<t>,<e>\>" | <f,t,e> <- flattenTransitions(spc)])
  when /Transition _ := spc.states;

private default str buildAllowedTransitionTuples(Spec s) = "";
  
private str buildEventsAsSingleRels(set[Spec] spcs)
  = "// Define each event as single relation so that the events can be used as variables in the constraints 
    '<for (r <- rels) {><r>
    '<}>"
    when
      set[str] rels := {buildSingleEventRel("<s.name>", e) | s <- spcs, /Event e := s.events};
    
private str buildSingleEventRel(str specName, Event e) 
  = "Event<capitalize(specName)><capitalize(event)> (event:id) = {\<event_<toLowerCase(specName)>_<toLowerCase(event)>\>}"
  when str event := replaceAll("<e.name>", "::", "_");

private str buildConstantRels(set[Spec] spcs) {
  return "__EMPTY (instance:id) = {}";

  //set[str] constRels = {};

  //for (/(Expr)`<Lit l>` := spcs) {
  //  switch (l) {
  //    case (Lit)`<Int i>`:            constRels += "__IntConst_<i> (const_<i>: int) = {\<<i>\>}";
  //    case (Lit)`<StringConstant s>`: constRels += "__StrConst_<unquote(s)> (const_<unquote(s)>: str) = {\<<s>\>}";
  //    case (Lit)`{}`:                 constRels += "__EMPTY (instance:id) = {}"; 
  //    case (Lit)`none`:               constRels += "__EMPTY (instance:id) = {}";
  //  }
  //}
  //
  //return "<for (r <- constRels) {><r>
  //       '<}>";  
}

private str unquote(StringConstant s) = "<s>"[1..-1];

private rel[str,str,str] flattenTransitions(Spec s)
  = {<"<cfrom>", "<cto>", "event_<name>_<event>"> | 
      str name := getLowerCaseSpecName(s),
      /(Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;` := s.states,
      str cfrom := convertFromState(from, name), str cto := convertToState(to, name),
      str event <- {toLowerCase(replaceAll("<e>", "::", "_")) | TransEvent e <- events}};

private str convertFromState((State)`(*)`, str _) = "state_uninitialized";
private default str convertFromState(rebel::lang::SpecSyntax::State st, str spec) = convertState(st, spec);   

private str convertToState((State)`(*)`, str _) = "state_finalized";
private default str convertToState(rebel::lang::SpecSyntax::State st, str spec) = convertState(st, spec);

private str convertState(rebel::lang::SpecSyntax::State st, str spec) = "state_<spec>_<toLowerCase(replaceAll("<st>", "::", "__"))>";   
  
str translateConfigState(Spec spc, uninitialized()) = "state_uninitialized";
str translateConfigState(Spec spc, finalized())     = "state_finalized";
str translateConfigState(Spec spc, state(str name)) = "state_<toLowerCase("<spc.name>")>_<toLowerCase(replaceAll("<name>", "::", "__"))>";

private str buildEventParamRels(set[Spec] specs, Config cfg, TModel tm) {
  list[str] rels = [];
  
  for (Spec s <- specs, e <- lookupEvents(s), /FormalParam p <- e.params) {
    rels += buildEventParamRel(s,e,p,cfg,tm);
  }
  
  return intercalate("\n", [r | r <- rels, r != ""]);
}

private str buildEventParamRel(Spec s, Event e, FormalParam p, Config cfg, TModel tm) {
  list[str] defs = ["cur:id", "nxt:id", getParamHeaderDef(p,cfg)];
  return "ParamEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)><getCapitalizedParamName(p)> (<intercalate(", ", defs)>) <buildParamTuples(s,e,p,cfg,tm)>";
}  

private str buildParamTuples(Spec s, Event e, FormalParam p, Config cfg, TModel tm) {
  void addTuple(int i, int j) {
    if (isPrim(p.tipe, tm)) {
      upperBound += "\<c<i>,c<j>,?\>";
    } else {
      for (str otherInst <- getInstancesOfType(p.tipe, cfg.instances<0,1>, tm)) {
        upperBound += "\<c<i>,c<j>,<otherInst>\>";
      }
    } 
  }

  list[str] upperBound = [];  
  for (int i <- [1..cfg.numberOfTransitions]) {
    addTuple(i, i+1);
  }
  
  if (!cfg.finiteTrace) {
    for (int i <- [cfg.numberOfTransitions..0]) {
      addTuple(cfg.numberOfTransitions, i);
    }  
  }

  return "\<= {<intercalate(",", upperBound)>}"; 
}

private str buildEnumRels(set[Spec] specs) {
  list[str] rels = ["<s.name>_<instance> (instance:id) = {\<<instance>\>}" | Spec s <- specs, /Id instance <- s.instances];
  return "<for (r <- rels) {><r>
         '<}>";
}

private str buildStateVectors(set[Spec] specs, Config cfg, TModel tm) {
  list[str] rels = [buildFieldRel(s, f, cfg, tm) | Spec s <- specs, /Field f <- s.fields];
  return "<for (r <- rels) {><r>
         '<}>";
}

private str buildFieldRel(Spec spc, Field f, Config cfg, TModel tm) {
  list[str] defs = ["config:id", "instance:id", getFieldHeaderDef(f,cfg)];
  return "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)> (<intercalate(", ", defs)>) <buildFieldTuples(spc, f, cfg, tm)>";
}

private str getFieldHeaderDef(Field f, Config cfg) = "<f.name>:<convertType(f.tipe)>"; 
private str getParamHeaderDef(FormalParam p, Config cfg) = "<p.name>:<convertType(p.tipe)>"; 

private str buildFieldTuples(Spec spc, Field f, Config cfg, TModel tm) {
  list[str] lowerBound = [];
  for (<str inst, "<f.name>", str val> <- cfg.initialValues[spc], val != "__none") {
    lowerBound += "\<c1,<inst>,<val>\>";
  }
  
  list[str] upperBound = [];  
  for (str inst <- lookupInstances(spc, cfg.instances<0,1>), int i <- [1..cfg.numberOfTransitions+1]) {
    if (!(i == 1 && /<inst, "<f.name>", "__none"> := cfg.initialValues[spc])) { // skip when the initial value should be 'none' or '{}'
      if (isPrim(f.tipe, tm)) {
        upperBound += "\<c<i>,<inst>,?\>";
      } else if (isSetOfInt(f.tipe, tm)) {
        for (int j <- [1..cfg.maxSizeIntegerSets+1]) {
          upperBound += "\<c<i>,<inst>,<inst>_elem<j>\>";
        }
      } else if (isSetOfString(f.tipe, tm)) {
        for (int j <- [1..cfg.maxSizeStringSets+1]) {
          upperBound += "\<c<i>,<inst>,<inst>_elem<j>\>";
        }
      }else { // Set of other specification
        for (str otherInst <- getInstancesOfType(f.tipe, cfg.instances<0,1>, tm)) {
          upperBound += "\<c<i>,<inst>,<otherInst>\>";
        }
      } 
    }
  }
  
  if (lowerBound != []) {
    return "\>= {<intercalate(",", lowerBound)>} \<= {<intercalate(",", upperBound)>}";
  } else {
    return "\<= {<intercalate(",", upperBound)>}";
  }
}


private str buildChangedInstancesRel(rel[Spec,str] instances, int numberOfTransitions, bool finiteTrace) { 
  list[str] tuples = ["\<c<c>,c<c+1>,<i>\>" | int c <- [1..numberOfTransitions], Spec s <- instances<0>, !isEmptySpec(s), str i <- instances[s]];
    
  if (!finiteTrace) {
    tuples += ["\<c<c>,c<j>,<i>\>" | int c <- [numberOfTransitions..0], int j <- [c..0], Spec s <- instances<0>, !isEmptySpec(s), str i <- instances[s]];
  }
    
  return "changedInstance (cur:id, nxt:id, instance:id) \<= {<intercalate(",", tuples)>}
         '";
}
  
private str buildRaisedEventsRel(rel[Spec spc, str instance] instances, int numberOfTransitions, bool finiteTrace) 
  = "raisedEvent (cur:id, nxt:id, event:id, instance:id) \<= {<intercalate(",", [tups | <spc, i> <- instances, str tups := buildRaisedEventsTuples(spc, i, numberOfTransitions, finiteTrace), tups != ""])>}";

private str buildRaisedEventsTuples(Spec spc, str instance, int numberOfTransitions, bool finiteTrace) {
  list[str] tuples = ["\<c<c>,c<c+1>,<toLowerCase(event)>,<instance>\>" | int c <- [1..numberOfTransitions], str event <- lookupRaisableEventName(spc)];
  
  if (!finiteTrace) {
    tuples += ["\<c<c>,c<j>,<toLowerCase(event)>,<instance>\>" | int c <- [numberOfTransitions..0], int j <- [c..0], str event <- lookupRaisableEventName(spc)];
  }
  
  return intercalate(",", tuples);
}

private str buildConfigRels(int numberOfTransitions, bool finiteTrace, bool exactNrOfSteps)
  = "Config (config:id) \>= {\<c1\>} \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    '<if (exactNrOfSteps) {>order (cur:id, nxt:id) = {<intercalate(",", ["\<c<i>,c<i+1>\>" | int i <- [1..numberOfTransitions]])>}<} else {>
    'order (cur:id, nxt:id) \<= {<intercalate(",", ["\<c<i>,c<i+1>\>" | int i <- [1..numberOfTransitions]])>}<}>
    'first (config:id) = {\<c1\>}
    'last (config:id) \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    'back (config:id) <if (finiteTrace) {>= {}<} else {> \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>} <}>
    'loop (cur:id, nxt:id) <if (finiteTrace) {>= {}<} else {> \<= {<intercalate(",", ["\<c<i>,c<j>\>" | int i <- [2..numberOfTransitions+1], int j <- [1..i+1]])>} <}>
    '";

private str buildInstanceRel(rel[Spec spc, str instance, State initialState] instances)
  = "Instance (spec:id, instance:id) = {<intercalate(",", ["\<<toLowerCase("<inst.spc.name>")>,<inst.instance>\>" | inst <- instances])>}";
  
private str buildInstanceInStateRel(rel[Spec spc, str instance, State state] instances, int numberOfTransitions) {
  str initialTup = buildInitialInstanceInStateTuples(instances);
  str iisRel = "instanceInState (config:id, instance:id, state:id) <if (initialTup != "") {>\>={<initialTup>}<}>\<= {<buildInstanceInStateTuples(instances<spc,instance>, numberOfTransitions)>}";
  return iisRel;
}

private str buildInitialInstanceInStateTuples(rel[Spec spc, str instance, State state] instances)
  = intercalate(",", ["\<c1,<i>,<translateConfigState(s, st)>\>" | <s,i,st> <- instances, !isEmptySpec(s), st != noState()]);

private str buildInstanceInStateTuples(rel[Spec spc, str instance] instances, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<toLowerCase(st)>\>" | int c <- [1..numberOfTransitions+1], <s,i> <- instances, str st <- lookupStateLabelsWithDefaultState(s)]);
  