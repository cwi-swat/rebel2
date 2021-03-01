module rebel::vis::ModuleVis

import rebel::lang::Syntax;
import rebel::lang::Parser;
import List;
import Set;
import IO;

import salix::App;
import salix::HTML;
import salix::Core;

import rebel::vis::SpecToSalixConverter;
import rebel::vis::salix::StateMachineCat;

alias Model = tuple[loc rebelFile, set[Spec] prevParsedSpecs];
  
App[Model] createStateMachineVis(loc rebelFile) {
  set[Spec] spcs = {s | /Spec s <- parseModule(rebelFile).parts};
  if (spcs == {}) {
    throw "No specification to visualize";
  }
  
  Model init() = <rebelFile, spcs>;
    
  return webApp(makeApp("rebelModVis", init, view, update, subs = changeCheckSubs),getHtmlLoc(), getStaticLoc());
}

private loc getHtmlLoc() = exists(|project://rebel2/|) ? |project://rebel2/salix/modulevis.html| : |plugin://rebel2/salix/modulevis.html|;
private loc getStaticLoc() = exists(|project://rebel2/|) ? |project://rebel2/salix/| : |plugin://rebel2/salix/|;

data Msg 
  = specChangedCheck(int time)
  ;
  
list[Sub] changeCheckSubs(str id, Model m) = [timeEvery(id, specChangedCheck, 1000)];

void view(Model m) {
  div(() {
    stateMachineCat("rebelVis", convertToSMJs(m.prevParsedSpecs));
  });
}

Model update(Msg msg, Model m) {
  switch (msg) {
    case specChangedCheck(_): {
      set[Spec] curSpcs = {s | /Spec s <- parseModule(m.rebelFile).parts};
      
      if (curSpcs != m.prevParsedSpecs) {
          m.prevParsedSpecs = curSpcs;
      }
    }
  }
  
  return m;
}

str convertToSMJs(loc spc) = convertToSMJs({s | /Spec s <- parseModule(spc).parts});

str convertToSMJs(set[Spec] spcs) {
  if ({Spec spc} := spcs) {
    // only a single specification in the module
    return "<spc.name> {
           '  <specToStateMachineJs(spc)>
           '};";
  } else {
    return "parallel[Label=\"\<\<Composite Machine\>\>\"] {    
           '  <intercalate(",", ["<s.name> { <specToStateMachineJs(s)> }" | Spec s <- spcs, /States _ := s.states] + ["#empty signature\n<s.name>" | Spec s <- spcs, /States _ !:= s.states])>;
           '};";    
  }
}



//str specToPlantUml(Spec spc) {
//  str conv(Spec spc) = conv(s) when /States s := spc.states;
//  
//  str conv((States)`states: <Transition* trans>`) = intercalate("\n", [c | t <- trans, str c := conv(t), c != ""]);
//  
//  str conv((Transition)`<State super> { <Transition* trans> }`) 
//    = "state <super> { <for (t <- trans, str c := conv(t), c != "") {>  
//      '  <c><}>
//      '}";
//  str conv((Transition)`(*) -\> <State to> : <{TransEvent ","}+ events>;`) 
//    = "[*] --\> <to> : <intercalate(", ", [conv(e) | e <- events])>";
//  str conv((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
//    = "<from> --\> [*] : <intercalate(", ", [conv(e) | e <- events])>";
//  str conv((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`) 
//    = "<from> --\> <to> : <intercalate(", ", [conv(e) | e <- events])>";
//  
//  str conv((TransEvent)`<Id event>`) = "<event>";
//  str conv((TransEvent)`<Id event>::<Id variant>`) = "<event>::<variant>";
//  
//  return 
//    "@startuml
//    'hide empty description
//    '<conv(spc)>
//    '@enduml";         
//}
