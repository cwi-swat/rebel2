module rebel::vis::SpecToSalixConverter

import rebel::lang::Syntax;
import List;
import Set; 
import String;
import IO;

data Filter
  = show()
  | valuesOnly()
  | hide()
  ;

str specToStateMachineJs(Spec spc, str instance = "", str activeState = "", str nextTrans = "", bool showValues = false, map[str,str] values = (), Filter \filter = show()) {
  set[str] done = {};
    
  str conv(Spec spc) = "<if (showValues) {><convValues()><}>
                       '<if (\filter != valuesOnly()) {><if (showValues) {>,<}> <convStates(s)>
                       '
                       '<convTrans(s)><} else {>;<}>"
                        when /States s := spc.states;
                        
  default str conv(Spec spc) = "";                         
  
  str actCol = "#dc3545";
  str nxtCol = "#007bff";
  str valCol = "#d6d8db";
    
  str prefix = instance == "" ? "<spc.name>" : instance;
  
  str labelAndActive(str label, str state) = "[Label=\"<label>\" color=\"<actCol>\" active]" when toLowerCase(state) == toLowerCase(activeState);
  default str labelAndActive(str label, str _) = "[Label=\"<label>\"]";
  
  str active(str state) = "[color=\"<actCol>\" active]" when state == activeState;
  default str active(str state) = "";
  
  str checkNext(str from, set[TransEvent] events) = "[color=\"<nxtCol>\"]" when toLowerCase(from) == toLowerCase(activeState), {e | TransEvent e <- events, "<e>" == nextTrans} != {};
  default str checkNext(str from, set[TransEvent] _) = "";
  
  str convValues() = "<prefix>.vals[Label=\"Values\" color=\"<valCol>\"]:
                     '  <intercalate("\n", ["<f>: <values[f]>" | f <- values])>"
                     when values != (); 
  default str convValues() = "<prefix>.vals[Label=\"Values\" color=\"<valCol>\"] : -";
  
  str convStates((States)`states: <Transition* trans>`) = "<intercalate(", ", toList({c | t <- trans, str c := convState(t), c != ""}))>;";
  str convState((Transition)`<State super> { <Transition* trans> }`) { 
    done += "<super>";
    return "<prefix>.<super>[Label=\"<super>\"] {  
           '  <intercalate(", ", dup([c | t <- trans, str c := convState(t), c != ""]))>;
           '}";
  }
  str convState((Transition)`<State super> <InnerStates inner> { <Transition* _> }`) { 
    done += "<super>";
    return "<super> {  
           '  <convState(inner)>;
           '}";
  }
  
  str convState((InnerStates)`[<{State ","}+ inner>]`) = intercalate(",", dup(["<prefix>.<s><labelAndActive("<s>", "<s>")>" | s <- inner]));
  str convState((Transition)`(*) -\> <State to> : <{TransEvent ","}+ _>;`) = "<prefix>.initial<active("initial")>" when "<to>" notin done; 
  str convState((Transition)`<State from> -\> (*) : <{TransEvent ","}+ _>;`) = "<prefix>.<from><labelAndActive("<from>","<from>")>, <prefix>.final<active("final")>" when "<from>" notin done; 
  str convState((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ _>;`) = "<prefix>.<from><labelAndActive("<from>","<from>")>" when "<from>" notin done;
  default str convState(Transition _) = ""; 
  
  str convTrans((States)`states: <Transition* trans>`) = intercalate("\n", [convTrans(t) | t <- trans]);
  str convTrans((Transition)`<State super> { <Transition* trans> }`) 
    = "<for (t <- trans) {><convTrans(t)>
      '<}>";
  str convTrans((Transition)`<State super> <InnerStates _> { <Transition* trans> }`) 
    = "<for (t <- trans) {><convTrans(t)>
      '<}>";

  str convTrans((Transition)`(*) -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "<prefix>.initial -\> <prefix>.<to><checkNext("initial", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
    = "<prefix>.<from> -\> <prefix>.final<checkNext("<from>", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> (*) : <{TransEvent ","}+ events>;`) 
    = "<prefix>.<from> -\> <prefix>.final<checkNext("<from>", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  str convTrans((Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`) 
    = "<prefix>.<from> -\> <prefix>.<to><checkNext("<from>", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";";
  
  str convEvent((TransEvent)`empty`) = "&#949;";
  str convEvent((TransEvent)`<Id event>`) = "<event>";
  str convEvent((TransEvent)`<Id event>::<Id variant>`) = "<event>::<variant>";
  
  str smCatStr = conv(spc);
  
  return smCatStr;
}