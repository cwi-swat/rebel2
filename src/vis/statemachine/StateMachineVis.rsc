module vis::statemachine::StateMachineVis

import rebel::lang::Syntax;
import rebel::lang::Parser;
import List;
import Set;

import salix::App;
import salix::HTML;
import salix::Core;
import salix::lib::UML;

import vis::statemachine::salix::StateMachineCat;

alias Model = tuple[loc spc, Spec prev];

App[Model] createVis(loc spc, int port) {
  if (/Spec s := parseModule(spc).parts) {
    Model init() = <spc, s>;

    return app(init, view, update, |http://localhost/statemachine/index.html|[port = port], |project://rebel2/salix/|, subs = changeCheckSubs);
  } else {
    throw "No defined specification in file";
  }
}

data Msg 
  = specChangedCheck(int time)
  ;
  
list[Sub] changeCheckSubs(Model m) = [timeEvery(specChangedCheck, 1000)];

void view(Model m) {
  div(() {
    stateMachineCat("rebelVis", specToStateMachineJs(m.prev));
  });
}

Model update(Msg msg, Model m) {
  switch (msg) {
      case specChangedCheck(_): {
        if (/Spec cur := parseModule(m.spc).parts) {
          if (cur != m.prev) {
            m.prev = cur;
          }
        }
      }
  }
  return m;
}

str specToStateMachineJs(Spec spc) {
  set[str] done = {};
  
  str conv(Spec spc) = "<convStates(s)>
                       '
                       '<convTrans(s)>"
                        when /States s := spc.states;
  
  str convStates((States)`states: <Transition* trans>`) = "<intercalate(", ", [c | t <- trans, str c := convState(t), c != ""])>;";
  str convState((Transition)`<State super> { <Transition* trans> }`) { 
    done += "<super>";
    return "<super> {  
           '  <intercalate(", ", dup([c | t <- trans, str c := convState(t), c != ""]))>;
           '}";
  }
  str convState((Transition)`<State super> <InnerStates inner> { <Transition* _> }`) { 
    done += "<super>";
    return "<super> {  
           '  <convState(inner)>;
           '}";
  }
  
  str convState((InnerStates)`[<{State ","}+ inner>]`) = intercalate(",", dup(["<s>" | s <- inner]));
  str convState((Transition)`(*) -\> <State to> : <{TransEvent ","}+ _>;`) = "" when "<to>" notin done; 
  str convState((Transition)`<State from> -\> (*) : <{TransEvent ","}+ _>;`) = "<from>" when "<from>" notin done; 
  str convState((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ _>;`) = "<from>" when "<from>" notin done;
  default str convState(Transition _) = ""; 
  
  str convTrans((States)`states: <Transition* trans>`) = intercalate("\n", [convTrans(t) | t <- trans]);
  str convTrans((Transition)`<State super> { <Transition* trans> }`) 
    = "<for (t <- trans) {><convTrans(t)>
      '<}>";
  str convTrans((Transition)`<State super> <InnerStates _> { <Transition* trans> }`) 
    = "<for (t <- trans) {><convTrans(t)>
      '<}>";

  str convTrans((Transition)`(*) -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "initial =\> <to> : \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
    = "<from> =\> final : \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
    = "<from> =\> final : \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "<from> =\> <to> : \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  
  str convEvent((TransEvent)`empty`) = "&#949;";
  str convEvent((TransEvent)`<Id event>`) = "<event>";
  str convEvent((TransEvent)`<Id event>::<Id variant>`) = "<event>::<variant>";
  
  return conv(spc);
}

str specToPlantUml(Spec spc) {
  str conv(Spec spc) = conv(s) when /States s := spc.states;
  
  str conv((States)`states: <Transition* trans>`) = intercalate("\n", [c | t <- trans, str c := conv(t), c != ""]);
  
  str conv((Transition)`<State super> { <Transition* trans> }`) 
    = "state <super> { <for (t <- trans, str c := conv(t), c != "") {>  
      '  <c><}>
      '}";
  str conv((Transition)`(*) -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "[*] --\> <to> : <intercalate(", ", [conv(e) | e <- events])>";
  str conv((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
    = "<from> --\> [*] : <intercalate(", ", [conv(e) | e <- events])>";
  str conv((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "<from> --\> <to> : <intercalate(", ", [conv(e) | e <- events])>";
  
  str conv((TransEvent)`<Id event>`) = "<event>";
  str conv((TransEvent)`<Id event>::<Id variant>`) = "<event>::<variant>";
  
  return 
    "@startuml
    'hide empty description
    '<conv(spc)>
    '@enduml";         
}
