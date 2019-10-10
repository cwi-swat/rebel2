module analysis::allealle::StaticRelationsTranslator

import lang::Syntax;
import analysis::allealle::CommonTranslationFunctions;

import String;
import List;

str translateStaticPart(set[Spec] spcs) {
  str def = "// Static configuration of state machines
            '<buildSpecRel(spcs)>
            '<buildStateRel(spcs)>
            '<buildAllowedTransitionRel(spcs)>
            '<buildEventsAsSingleRels(spcs)>"; 

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
    'State (state:id) = {\<state_uninitialized\>,\<state_finalized\>,<stateTuples>}
    'initialized (state:id) = {<stateTuples>}
    'finalized (state:id) = {\<state_finalized\>}
    'uninitialized (state:id) = {\<state_uninitialized\>}
    '<buildIndividualStateRels(spcs)>"
  when stateTuples := intercalate(",", [buildStateTuples(s) | s <- spcs]);

private str buildIndividualStateRels(set[Spec] spcs)
  = "<for (s <- spcs) {><buildIndividualStateRel(s)>
    '<}>";

private str buildIndividualStateRel(Spec spc)
  = "<for (lang::Syntax::State s <- states) {>State<getCapitalizedSpecName(spc)><capitalize("<s>")> (state:id) = {\<<getStateLabel(spc, s)>\>}<}>"
    when set[lang::Syntax::State] states := lookupStates(spc);
  
private str buildStateTuples(Spec spc) 
  = intercalate(",", ["\<state_<s>\>" | str s <- states])
  when 
    str name := getLowerCaseSpecName(spc),
    set[str] states := {"<name>_<toLowerCase("<s.name>")>" | /lang::Syntax::State s := spc.states, s has name};

private str buildAllowedTransitionRel(set[Spec] spcs)
  = "// Define which transitions are allowed (in the form of `from a state` -\> ` via an event` -\> `to a state`
    'allowedTransitions (from:id, to:id, event:id) = {<intercalate(",",[buildAllowedTransitionTuples(s) | s <- spcs])>}";

private str buildAllowedTransitionTuples(Spec spc)
  = intercalate(",", ["\<<f>,<t>,<e>\>" | <f,t,e> <- flattenTransitions(spc)]);
  
private str buildEventsAsSingleRels(set[Spec] spcs)
  = "// Define each event as single relation so that the events can be used as variables in the constraints 
    '<for (r <- rels) {><r>
    '<}>"
    when
      set[str] rels := {buildSingleEventRel("<s.name>", e) | s <- spcs, /Event e := s.events};
    
private str buildSingleEventRel(str specName, Event e) 
  = "Event<capitalize(specName)><capitalize(event)> (event:id) = {\<event_<toLowerCase(specName)>_<toLowerCase(event)>\>}"
  when str event := replaceAll("<e.name>", "::", "_");

private rel[str,str,str] flattenTransitions(Spec s)
  = {<"<cfrom>", "<cto>", "event_<name>_<event>"> | 
      str name := getLowerCaseSpecName(s),
      /(Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;` := s.states,
      str cfrom := convertFromState(from, name), str cto := convertToState(to, name),
      str event <- {toLowerCase(replaceAll("<e>", "::", "_")) | TransEvent e <- events}};

private str convertFromState((State)`(*)`, str _) = "state_uninitialized";
private default str convertFromState(lang::Syntax::State st, str spec) = convertState(st, spec);   

private str convertToState((State)`(*)`, str _) = "state_finalized";
private default str convertToState(lang::Syntax::State st, str spec) = convertState(st, spec);

private str convertState(lang::Syntax::State st, str spec) = "state_<spec>_<toLowerCase("<st>")>";   
