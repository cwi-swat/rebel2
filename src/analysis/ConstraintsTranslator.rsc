module analysis::ConstraintsTranslator

import lang::Syntax;
import analysis::CommonTranslationFunctions;
import analysis::FormulaAndExpressionTranslator;

import String;
import IO;
import Set;
import List;
import IO;
import ParseTree;

str translateConstraints(set[Spec] spcs) {
  str cons = "<genericTypeConstraints()>
             '<machineTypeConstraints(spcs)>
             '<allConfigsAreReachable()>
             '<onlyOneTriggeringEvent()>
             '<noMachineWithoutState()>
             '<machineOnlyHasValuesWhenInitialized(spcs)>
             '<noTransitionsBetweenUnrelatedStates()>
             '<transitionFunction(spcs)>
             '<encodeAsserts()>
             '<findMinimumExample(spcs)>
             '";
  
  return cons;
}

private str genericTypeConstraints() 
  = "
    '// Generic \'Type\' constraints
    'order in Config[config as cur] x Config[config as nxt]
    'raisedEvent in order x allowedTransitions[event] x Instance[instance]
    'instanceInState in Instance[instance] x Config x State
    'changedInstance in order x Instance[instance]
    ";
    
private str machineTypeConstraints(set[Spec] spcs)
  = "// Machine specific \'Type\' constraints
    '<for (Spec s <- spcs) {>StateVector<getCapitalizedSpecName(s)>Primitives[config,instance] in Config x Instance[instance]
    '<}>";
    
private str allConfigsAreReachable()
  = "// Generic: All configurations are reachable
    'forall c : Config - InitialConfig | c in (InitialConfig[config as cur] |x| ^\<cur,nxt\>order)[nxt -\> config]
    '";
    
private str onlyOneTriggeringEvent()
  = "// Generic: Every transition can only happen by exactly one event
    'forall o : order | one o |x| raisedEvent
    '";
    
private str noMachineWithoutState()
  = "// Generic: In every configuration all machines have a state
    'forall c : Config, inst : Instance | one instanceInState |x| c |x| inst
    '"; 
    
private str machineOnlyHasValuesWhenInitialized(set[Spec] spcs)
  = "// Specific per machine: In every configuration iff a machine is in an initialized state then it must have values
    '<for (Spec s <- spcs) {>forall c : Config, inst : (Instance |x| <getCapitalizedSpecName(s)>)[instance] | (((c x inst) |x| instanceInState)[state] ⊆ initialized \<=\> one StateVector<getCapitalizedSpecName(s)>Primitives |x| c |x| inst)
    '<}>
    '";
    
private str noTransitionsBetweenUnrelatedStates() 
  = "// Generic: Transitions are only allowed between if an event is specified between two states
    'forall o : order |x| raisedEvent | (o[cur as config] ⨝ instanceInState)[state-\>from] x (o[nxt as config] ⨝ instanceInState)[state-\>to] x o[event] ⊆ allowedTransitions
    '";

private str transitionFunction(set[Spec] spcs) {
  str trans = 
    "// Transition function
    'forall o : order |  
    '  <for (Spec s <- spcs) {>// Possible transitions for <s.name>
    '  (
    '    <transitionFunction(s, "o")>
    '  )
    '  <}>
    '";
  
  return trans;
}

private str transitionFunction(Spec spc, str step) 
  = "forall inst : (Instance |x| <getCapitalizedSpecName(spc)>)[instance] |  
    '  let cur = (<step>[cur as config] |x| <getPrimStateVectorName(spc)> |x| instanceInState |x| inst)[config -\> curConfig, state-\>curState, instance-\>curInstance, <selectAndRenamePrimFields(spc, "cur")>],
    '      nxt = (<step>[nxt as config] |x| <getPrimStateVectorName(spc)> |x| instanceInState |x| inst)[config -\> nxtConfig, state-\>nxtState, instance-\>instance, <selectAndRenamePrimFields(spc, "nxt")>] | 
    // Iff this is the instance that raised the event then one of the transitions must have happened 
    (some nxt[instance] & ((raisedEvent |x| <step>)[instance]) \<=\> 
      (
        <translateEvents(spc, "cur", "nxt")>
      )
    ) 
    &&
    // If it is not a transitioning instance, frame the values
    (no nxt[instance] & (raisedEvent |x| <step>)[instance] \<=\> 
      (
        // The instance keeps its current state
        (<step>[nxt-\>config] |x| instanceInState |x| inst)[state] = (<step>[cur-\>config] |x| instanceInState |x| inst)[state] 
        && (
          // Either there was no values attached yet 
          (no (o[nxt-\>config] ⨝ <getPrimStateVectorName(spc)> |x| inst)) 
          || 
          // Or keep the current values
          <frameValues(spc, "cur", "nxt")>
        )
    )) 
  ";

private str selectAndRenamePrimFields(Spec spc, str prefix)
  = intercalate(", ", ["<f>-\><prefix><capitalize(f)>" | str f <- lookupPrimitiveFieldNames(spc)]);
   
private str translateEvents(Spec spc, str cur, str nxt) 
  = "<intercalate("\n||\n", [translateEvent("<spc.name>", e,cur,nxt) | Event e <- events])>"
  when set[Event] events := lookupEvents(spc);

private str translateEvent(str spc, Event event, str cur, str nxt) 
  =  "( // Event <spc>.<event.name>
     '  <pre> <if (pre != "") {>&&<}>
     '  <post> <if (post != "") {>&&<}>
     '  <translateGenericPart(spc, event, cur, nxt)>
     ')"
  when   
    str pre := translatePre(spc, event, cur, nxt),
    str post := translatePost(spc, event, cur, nxt);

private str translatePre(str spc, Event event, str cur, str nxt) 
  = " // Preconditions 
    ' <intercalate(" &&\n",[translate(f,ctx(cur,nxt,spc,"<event.name>")) | f <- pre.formulas])>"
    when /Pre pre := event;

private default str translatePre(str spc, Event event, str cur, str nxt) = "";     

private str translatePost(str spc, Event event, str cur, str nxt) 
  = " // Postconditions
    ' <intercalate(" &&\n", [translate(f, ctx(cur,nxt,spc,"<event.name>")) | Formula f <- post.formulas])>"
    when /Post post := event;

private default str translatePost(str spc, Event event, str cur, str nxt) = "";     

private str translateGenericPart(str spc, Event event, str cur, str nxt)
  = "(o |x| raisedEvent)[event] = <eventName> &&
    'nxt[nxtState] = ((o[cur-\>config] |x| instanceInState |x| inst)[state as from] |x| (allowedTransitions |x| <eventName>))[to-\>nxtState] && 
    '(changedInstance |x| o)[instance] = nxt[instance] // TODO: needs to be extended when syncing events is introduced"
  when str eventName := "Event<capitalize(spc)><capitalize("<event.name>")>";  
    
private str frameValues(Spec spc, str cur, str nxt) 
  = "(some (<nxt> x <cur>) where (<intercalate(" && ", ["(<nxt><ff> = <cur><ff>)" | str f <- lookupPrimitiveFieldNames(spc), str ff := capitalize(f)])>))";

private str encodeAsserts() 
  = "// Asserts: this is where the checks get added
    'exists c: Config, p: StateVectorPingPongPrimitives | some p where times = 18
    '";

private str findMinimumExample(set[Spec] spcs) 
  = "objectives: minimize(Config[count()])"; // Todo minimize parameter relations as well