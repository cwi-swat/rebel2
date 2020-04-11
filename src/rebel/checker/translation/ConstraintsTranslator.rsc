module rebel::checker::translation::ConstraintsTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::translation::EventTranslator;
import rebel::checker::translation::FormulaAndExpressionTranslator;
import rebel::checker::translation::RelationCollector;
import rebel::checker::Rebel2Alle;

import String;
import IO;
import Set;
import List;
import IO;
import ParseTree;

str translateConstraints(Config cfg, AlleAlleSnippet snippets, set[Spec] spcs) 
  = "<configurationConstraints(cfg.finiteTrace)>
    '<genericTypeConstraints(cfg.finiteTrace)>
    '<machineFieldTypeConstraints(snippets)>
    '<eventParamTypeAndMultiplicityConstraints(snippets)>
    '<allConfigsAreReachable()>
    '<onlyOneTriggeringEvent(cfg.finiteTrace)>
    '<noMachineWithoutState(spcs)>
    '<machineOnlyHasValuesWhenInitialized(snippets)>
    '<noTransitionsBetweenUnrelatedStates(cfg.finiteTrace)>
    '<changeSetPredicates(spcs)>
    '<helperPredicates()>
    '<translateEventPredicates(snippets)>
    '<translatePartialTransitionFunctions(snippets)>
    '<translateCompleteTransitionFunction(spcs, cfg)>
    '";

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
    
private str machineFieldTypeConstraints(AlleAlleSnippet snippets) 
  = "// Machine specific `type` constraints
    '<for (str spc <- snippets.typeCons<0>) {>// For `<spc>`
    '<for (tc <- snippets.typeCons[spc]) {><tc>
    '<}><}>";
       
private str machineOnlyHasValuesWhenInitialized(AlleAlleSnippet snippets) 
  = "// Specific per machine: In every configuration iff a machine is in an initialized state then it must have values
    '<for (str spc <- snippets.fieldMultiplicityCons<0>) {>// for `<spc>`
    '<for (str cons <- snippets.fieldMultiplicityCons[spc]) {><cons>
    '<}><}>";

private str eventParamTypeAndMultiplicityConstraints(AlleAlleSnippet snippets) 
  = "<if (snippets.paramMultiplicityCons != {}) {>
    '// Specific per event: parameter multiplicity constraints
    '∀ step ∈ (order ∪ loop) ⨝ raisedEvent | (
    '  <intercalate(" ∧\n", toList(snippets.paramMultiplicityCons<1>))>
    ')<}>";

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
