module analysis::allealle::ConstraintsTranslator

import rebel::lang::SpecSyntax;
import rebel::lang::SpecTypeChecker;

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::EventTranslator;
import analysis::allealle::SyncedEventGraphBuilder;

import String;
import IO;
import Set;
import List;
import IO;
import ParseTree;

str translateConstraints(set[Spec] spcs, Config cfg, str check) {
  str cons = "<genericTypeConstraints()>
             '<machineFieldTypeConstraints(spcs, cfg)>
             '<eventParamTypeAndMultiplicityConstraints(spcs, cfg)>
             '<allConfigsAreReachable()>
             '<onlyOneTriggeringEvent()>
             '<noMachineWithoutState()>
             '<machineOnlyHasValuesWhenInitialized(spcs, cfg)>
             '<noTransitionsBetweenUnrelatedStates()>
             '<helperPredicates()>
             '<translateEventPredicates(spcs, cfg)>
             '<transitionFunction(spcs, cfg)>
             '<encodeAsserts(check)>
             '<findMinimumExample(spcs)>
             '";
  
  return cons;
}

private str genericTypeConstraints() 
  = "
    '// Generic \'Type\' constraints
    'order ⊆ Config[config as cur] ⨯ Config[config as nxt]
    'raisedEvent ⊆ order ⨯ allowedTransitions[event] ⨯ Instance[instance]
    'instanceInState ⊆ Instance[instance] ⨯ Config ⨯ State
    'changedInstance ⊆ order ⨯ Instance[instance]
    ";
    
private str machineFieldTypeConstraints(set[Spec] spcs, Config cfg) {
  list[str] typeCons = [];
  
  for (Spec spc <- spcs, /Field f <- spc.fields) {    
    if (isPrim(f.tipe, cfg.tm)) {
      typeCons += "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>[config,instance]  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance]";
    } else {
      typeCons += "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] ⨯ (Instance ⨝ <f.tipe.tp>)[instance-\><f.name>]";
    }
  } 
  
  return "// Machine specific `type` constraints
         '<for (tc <- typeCons) {><tc>
         '<}>";
}
   
private str allConfigsAreReachable()
  = "// Generic: All configurations are reachable
    '∀ c ∈ Config ∖ InitialConfig | c ⊆ (InitialConfig[config as cur] ⨝ ^\<cur,nxt\>order)[nxt -\> config]
    '";
    
private str onlyOneTriggeringEvent()
  = "// Generic: Every transition can only happen by exactly one event
    '∀ o ∈ order | one o ⨝ raisedEvent
    '";
    
private str noMachineWithoutState()
  = "// Generic: In every configuration all machines have a state
    '∀ c ∈ Config, inst ∈ Instance | one instanceInState ⨝ c ⨝ inst
    '"; 
    
private str machineOnlyHasValuesWhenInitialized(set[Spec] spcs, Config cfg) {
  list[str] cons = [];
  
  for (Spec s <- spcs, /Field f <- s.fields) {    
    str relName = "<getCapitalizedSpecName(s)><getCapitalizedFieldName(f)>";
    
    if (isPrim(f.tipe,cfg.tm)) {
      cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇔ one <relName> ⨝ c ⨝ inst)"; 
    } else {
      str mult = (setType(_) := getType(f,cfg.tm)) ? "some" : "one";
    
      cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇔ <mult> <relName> ⨝ c ⨝ inst)";  
      //cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (no (((c ⨯ inst) ⨝ instanceInState)[state] ∩ initialized) ⇒ no <relName> ⨝ c ⨝ inst)";  
    }
  } 
  
  return "// Specific per machine: In every configuration iff a machine is in an initialized state then it must have values
         '<for (c <- cons) {><c>
         '<}>
         '";
}

private str eventParamTypeAndMultiplicityConstraints(set[Spec] spcs, Config cfg) {
  list[str] typeCons = [];
  list[str] multCons = [];

  for (Spec spc <- spcs, Event ev <- spc.events, /FormalParam p <- ev.params) {
    str relName = "ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>";

    if (isPrim(p.tipe, cfg.tm)) {
      typeCons += "<relName>[cur,nxt] ⊆ order";
      multCons += "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ one (step ⨝ <relName>))"; 
    } else {
      typeCons += "<relName> ⊆ order ⨯ (Instance ⨝ <p.tipe.tp>)[instance-\><toLowerCase("<p.name>")>]";

      str mult = (setType(_) := getType(p, cfg.tm)) ? "some" : "one";
      multCons += "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ <mult> (step ⨝ <relName>))";                 
    }
  }
  
  return "<intercalate("\n", typeCons)>
         '<if (multCons != []) {>
         '// Specific per event
         '∀ step ∈ order ⨝ raisedEvent | (
         '  <intercalate(" ∧\n", multCons)>
         ')<}>
         '";
}
   
private str noTransitionsBetweenUnrelatedStates() 
  = "// Generic: Transitions are only allowed between if an event is specified between two states
    '∀ o ∈ order ⨝ raisedEvent | (o[cur as config] ⨝ instanceInState)[state-\>from] ⨯ (o[nxt as config] ⨝ instanceInState)[state-\>to] ⨯ o[event] ⊆ allowedTransitions
    '";

private str helperPredicates() 
  = "// Generic predicates
    'pred forceState[curState: (state:id), nxtState: (state:id), raisedEvent: (event:id)]
    '  = nxtState = (curState[state as from] ⨝ (allowedTransitions ⨝ raisedEvent))[to-\>state]
    '
    'pred inState[config: (config:id), instance: (instance:id), state: (state:id)]
    '  = ((instance ⨯ config) ⨝ instanceInState)[state] ⊆ state
    '";
  

private str translateEventPredicates(set[Spec] spcs, Config cfg) {
  Graph[SyncedWith] syncDep = buildSyncGraph(spcs, cfg.tm);
  
  return "<for (Spec s <- spcs) {><translateEventsToPreds(s, cfg)>
         '<constructTransitionFunction(s, syncDep, cfg)>
         '<}>";
}

private str transitionFunction(set[Spec] spcs, Config cfg) 
  = "// Transition function
    '∀ step ∈ order | <intercalate(" ∧ ", ["possibleTransitions<getCapitalizedSpecName(s)>[step]" | s <- spcs])>
    '";  

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";
    
private str encodeAsserts(str check) 
  = "// Asserts: this is where the checks get added
    '<check>
    '";

private str findMinimumExample(set[Spec] spcs) 
  = "// Minimize the number of steps by minimizing the number of Configurations
    'objectives: minimize Config[count()]"; 
