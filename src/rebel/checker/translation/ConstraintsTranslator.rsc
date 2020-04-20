module rebel::checker::translation::ConstraintsTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::translation::EventTranslator;
import rebel::checker::translation::FormulaAndExpressionTranslator;
import rebel::checker::translation::RelationCollector;
import rebel::checker::ConfigTranslator;

import String;
import IO;
import Set;
import List;
import ParseTree;

str translateConstraints(rebel::checker::ConfigTranslator::Config cfg, set[Spec] spcs, TModel tm, RelMapping rm) 
  = "<configurationConstraints(cfg.finiteTrace)>
    '<genericTypeConstraints(cfg.finiteTrace)>
    '<machineFieldTypeConstraints(spcs, tm)>
    '<eventParamTypeAndMultiplicityConstraints(spcs, tm)>
    '<allConfigsAreReachable()>
    '<onlyOneTriggeringEvent(cfg.finiteTrace)>
    '<noMachineWithoutState(spcs)>
    '<machineOnlyHasValuesWhenInitialized(spcs, tm)>
    '<noTransitionsBetweenUnrelatedStates(cfg.finiteTrace)>
    '<changeSetPredicates(spcs)>
    '<helperPredicates()>
    '<translateEventsToPreds(spcs, rm, tm)>
    '<constructTransitionFunctions(spcs, rm, tm)>
    '<translateCompleteTransitionFunction(spcs, cfg)>";

private str configurationConstraints(bool finiteTrace) 
  = "
    '// Constraints for the configuration and ordering relations
    'order ⊆ Config[config as cur] ⨯ Config[config as nxt]
    'last = Config ∖ order[cur-\>config]  // There is only one last configuration
    '<if (!finiteTrace) {>back ⊆ Config 
    'lone back 
    'some loop  
    'loop ⊆ last[config as cur] ⨯ back[config as nxt] // Loop contains at most one tuple going back from the last configuration to the<}> 
    '";

private str genericTypeConstraints(bool finiteTrace) 
  = "// Generic \'Type\' constraints    
    'raisedEvent ⊆ (order<if (!finiteTrace) {> ∪ loop<}>) ⨯ allowedTransitions[event] ⨯ Instance[instance]
    'instanceInState ⊆ Instance[instance] ⨯ Config ⨯ State
    'changedInstance ⊆ (order<if (!finiteTrace) {> ∪ loop<}>) ⨯ Instance[instance]
    ";
    
private str machineFieldTypeConstraints(set[Spec] specs, TModel tm) {
  rel[Spec,str] cons = {};
  
  for (Spec spc <- specs, /Field f <- spc.fields) {
    if (isPrim(f.tipe, tm)) {
      cons += <spc, "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>[config,instance]  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance]">;
    } else {
      cons += <spc, "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>  ⊆ Config ⨯ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] ⨯ (Instance ⨝ <getSpecOfType(f.tipe, tm)>)[instance-\><f.name>]">;    
    }
  }
 
  return "// Machine specific `type` constraints
         '<for (Spec spc <- cons<0>) {>// For `<spc.name>`
         '<for (str fc <- cons[spc]) {><fc>
         '<}><}>";
} 
           
private str machineOnlyHasValuesWhenInitialized(set[Spec] spcs, TModel tm) {
  str cons = "// Specific per machine: In every configuration iff a machine is in an initialized state then it must have values\n";
  
  for (Spec s <- spcs) {
    cons += "// for <s.name>\n"; 
    
    for (/Field f <- s.fields) {    
      str relName = "<getCapitalizedSpecName(s)><getCapitalizedFieldName(f)>";
      
      if (isPrim(f.tipe, tm)) {
        cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇔ one <relName> ⨝ c ⨝ inst)\n"; 
      } else {
        cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (no (((c ⨯ inst) ⨝ instanceInState)[state] ∩ initialized) ⇒ no <relName> ⨝ c ⨝ inst)\n";  
  
        if (setType(_) !:= getType(f, tm) && optionalType(_) !:= getType(f, tm)) {
          cons += "∀ c ∈ Config, inst ∈ (Instance ⨝ <getCapitalizedSpecName(s)>)[instance] | (((c ⨯ inst) ⨝ instanceInState)[state] ⊆ initialized ⇒ one <relName> ⨝ c ⨝ inst)\n";  
        }
      }
    }
  } 

  return cons;
} 

private str eventParamTypeAndMultiplicityConstraints(set[Spec] spcs, TModel tm) {
  rel[Spec,str] typeCons = {};
  rel[Spec,str] multCons = {};

  for (Spec spc <- spcs, Event ev <- spc.events, /FormalParam p <- ev.params) {
    str relName = "ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)><getCapitalizedParamName(p)>";

    if (isPrim(p.tipe, tm)) {
      typeCons[spc] = "<relName>[cur,nxt] ⊆ order ∪ loop";
      multCons[spc] = "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ one (step ⨝ <relName>))"; 
    } else {
      typeCons[spc] = "<relName> ⊆ (order ∪ loop) ⨯ (Instance ⨝ <p.tipe.tp>)[instance-\><p.name>]";

      str mult = (setType(_) := getType(p, tm)) ? "some" : "one";
      multCons[spc] = "(some (step ⨝ Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(ev)>) ⇔ <mult> (step ⨝ <relName>))";                 
    }
  }

  return "// Specific per event: parameter type and multiplicity constraints
         '<for (Spec spc <- typeCons<0>) {>// Type constraints for events of <spc.name>
         '<for (str tc <- typeCons[spc]) {><tc>
         '<}><}>
         '<if (multCons != {}) {>// Multiplicity constraints for event parameters
         '∀ step ∈ (order ∪ loop) ⨝ raisedEvent | (
         '  <intercalate(" ∧\n", toList(multCons<1>))>
         ')<}>";
} 

private str allConfigsAreReachable()
  = "// Generic: All configurations are reachable
    '∀ c ∈ Config ∖ first | c ⊆ (first[config as cur] ⨝ ^\<cur,nxt\>order)[nxt -\> config]
    '";
    
private str onlyOneTriggeringEvent(bool finiteTrace)
  = "// Generic: Every transition can only happen by exactly one event
    '∀ o ∈ order<if (!finiteTrace) {> ∪ loop<}> | one o ⨝ raisedEvent
    '";
    
private str noMachineWithoutState(set[Spec] spcs)
  = "// Specif: In every configuration all machines have a state IFF its a machine which is not empty
    '∀ c ∈ Config, inst ∈ <nonEmptyMachineInstances(spcs)> | one instanceInState ⨝ c ⨝ inst
    '"; 

private str nonEmptyMachineInstances(set[Spec] spcs) {
  list[str] emptyMachines = [];
  for (Spec s <- spcs, isEmptySpec(s)) {
    emptyMachines += "<s.name>";
  }
  
  if (emptyMachines == []) {
    return "Instance";
  } else {
    return "(Instance ∖ ((<intercalate(" ∪ ", emptyMachines)>) ⨝ Instance))";
  }
}   
   
private str noTransitionsBetweenUnrelatedStates(bool finiteTrace) 
  = "// Generic: Transitions are only allowed between if an event is specified between two states
    '∀ o ∈ (order<if (!finiteTrace) {> ∪ loop<}>) ⨝ raisedEvent | (o[cur as config] ⨝ instanceInState)[state-\>from] ⨯ (o[nxt as config] ⨝ instanceInState)[state-\>to] ⨯ o[event] ⊆ allowedTransitions
    '";

private str changeSetPredicates(set[Spec] spcs) 
  = "// Change set predicates
    'pred inChangeSet[step: (cur:id, nxt:id), instances: (instance:id)]
    '  = instances ⊆ (changedInstance ⨝ step)[instance]
    ' 
    'pred notInChangeSet[step: (cur:id, nxt:id), instances: (instance:id)]
    '  = no instances ∩ (changedInstance ⨝ step)[instance]
    '
    'pred changeSetCanContain[step: (cur:id, nxt:id), instances: (instance:id)]
    '  = (changedInstance ⨝ step)[instance] ⊆ instances <if (freeInstances != []) {>∪ <intercalate(" ∪ ", freeInstances)><}>
    '"
    when list[str] freeInstances := ["<s.name>_<inst>" | Spec s <- spcs, /Instances instances <- s.instances, /(Instance)`<Id inst>*` <- instances.instances];


private str helperPredicates() 
  = "// Generic predicates
    'pred forceState[curState: (state:id), nxtState: (state:id), raisedEvent: (event:id)]
    '  = nxtState = (curState[state as from] ⨝ (allowedTransitions ⨝ raisedEvent))[to-\>state]
    '
    'pred inState[config: (config:id), instance: (instance:id), state: (state:id)]
    '  = ((instance ⨯ config) ⨝ instanceInState)[state] ⊆ state
    '";
  
private bool hasTransitions(Spec s) = /Transition _ := s.states;

private str translateEventPredicates(AlleAlleSnippet snippets) 
  = "<for (str spc <- snippets.eventPred<0>) {>// Event predicates for `<spc>`
    '<for (str ep <- snippets.eventPred[spc]) {><ep>
    '<}><}>";

private str translatePartialTransitionFunctions(AlleAlleSnippet snippets) 
  = "<for (str spc <- snippets.transPred<0>) {>// Transition function for `<spc>`
    '<snippets.transPred[spc]>
    '<}>";
  
private str translateCompleteTransitionFunction(set[Spec] spcs, Config cfg) 
  = "// Transition function
    '∀ step ∈ order<if (!cfg.finiteTrace) {> ∪ loop<}>| <intercalate(" ∧ ", ["possibleTransitions<getCapitalizedSpecName(s)>[step]" | s <- spcs, hasTransitions(s)])>
    '";  

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";
