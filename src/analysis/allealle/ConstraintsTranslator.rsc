module analysis::allealle::ConstraintsTranslator

import lang::Syntax;
import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::EventTranslator;
import analysis::Checker;

import String;
import IO;
import Set;
import List;
import IO;
import ParseTree;

str translateConstraints(set[Spec] spcs, Config cfg, str check) {
  str cons = "<genericTypeConstraints()>
             '<machineTypeConstraints(spcs)>
             '<eventParamTypeAndMultiplicityConstraints(spcs, cfg)>
             '<allConfigsAreReachable()>
             '<onlyOneTriggeringEvent()>
             '<noMachineWithoutState()>
             '<machineOnlyHasValuesWhenInitialized(spcs)>
             '<noTransitionsBetweenUnrelatedStates()>
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
    
private str machineTypeConstraints(set[Spec] spcs)
  = "// Machine specific \'Type\' constraints
    '<for (Spec s <- spcs) {>SV<getCapitalizedSpecName(s)>OnePrims[config,instance] ⊆ Config ⨯ Instance[instance]
    '<}>";
   
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
    
private str machineOnlyHasValuesWhenInitialized(set[Spec] spcs)
  = "// Specific per machine: In every configuration iff a machine is in an initialized state then it must have values
    '<for (Spec s <- spcs) {>∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇔ one SV<getCapitalizedSpecName(s)>OnePrims ⨝ c ⨝ inst)
    '<}>
    '";

private str eventParamTypeAndMultiplicityConstraints(set[Spec] spcs, Config cfg) {
  list[str] typeCons = [];
  list[str] multCons = [];

  for (Spec spc <- spcs, Event ev <- spc.events) {
    if (size(lookupPrimitiveParams(ev, cfg.tm)) > 0) {
      typeCons += "ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>Primitives[cur,nxt] ⊆ order";
      multCons += "(some (o ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇒ one (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>Primitives))";                 
    }
    
    for (FormalParam p <- lookupNonPrimParams(ev, cfg.tm)) {
      typeCons += "ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)> ⊆ order ⨯ (Instance ⨝ <p.tipe.tp>)[instance-\><toLowerCase("<p.name>")>]";

      str mult = (/(Multiplicity)`set` := p.tipe) ? "some" : "one";
      multCons += "(some (o ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇒ <mult> (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>))";                 
    }
  }
  
  return "<intercalate("\n", typeCons)>
         '// Specific per event
         '∀ o ∈ order ⨝ raisedEvent | (
         '  <intercalate(" ∧\n", multCons)>
         ')";
}
   
private str noTransitionsBetweenUnrelatedStates() 
  = "// Generic: Transitions are only allowed between if an event is specified between two states
    '∀ o ∈ order ⨝ raisedEvent | (o[cur as config] ⨝ instanceInState)[state-\>from] ⨯ (o[nxt as config] ⨝ instanceInState)[state-\>to] ⨯ o[event] ⊆ allowedTransitions
    '";

private str transitionFunction(set[Spec] spcs, Config cfg) {
  str trans = 
    "// Transition function
    '∀ o ∈ order |  
    '  <intercalate("\n ∧ \n", ["(
                                '  <transitionFunction(s, cfg)>
                                ')" | s <- spcs])>
    '";
  
  return trans;
}

private str transitionFunction(Spec spc, Config cfg) 
  = "// Events from <getCapitalizedSpecName(spc)>  
    '∀ inst ∈ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] |  
    '  // Iff this is the instance that raised the event then one of the transitions must have happened 
    '  (some inst ∩ ((raisedEvent ⨝ o)[instance]) ⇔ 
    '    <translateEvents(spc, "inst", cfg)>
    '  ) 
    '  ∧
    '  // Iff it is not a transitioning instance, frame the values
    '  (no inst ∩ (changedInstance ⨝ o)[instance] ⇔
    '    <translateFrameEvent(spc, getFrameEvent(spc), "inst", cfg)>
    '  )"; 

private str translateEvents(Spec spc, str instRel, Config cfg) 
  = "<intercalate("\n ∨ \n", [translateEvent(spc, e, instRel, cfg) | Event e <- events, !isFrameEvent(e)])>"
  when set[Event] events := lookupEvents(spc);

private Event getFrameEvent(Spec spc) {
  for (Event e <- lookupEvents(spc), isFrameEvent(e)) {
    return e;
  }
  
  throw "No frame event found in `<spc.name>`";
}  

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";
    
private str encodeAsserts(str check) 
  = "// Asserts: this is where the checks get added
    '<check>
    '";

private str findMinimumExample(set[Spec] spcs) {
  // minimize all Parameter relations to minimize junk
  return "objectives: minimize Config[count()]"; 
}
