module rebel::vis::SpecToSalixConverter

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import List;
import Set; 
import String;
//import IO;

data Filter
  = show()
  | valuesOnly()
  | hide()
  ;

str specToStateMachineJs(Spec spc, str instance = "", str activeState = "", str nextTrans = "", bool showValues = false, map[str,str] values = (), Filter \filter = show()) {
  str conv(Spec spc) = "<if (showValues) {><convValues()><}>
                       '<if (\filter != valuesOnly()) {><if (showValues) {>,<}> <convLifeCycle(s)>
                       '<} else {>;<}>"
                        when /States s := spc.states;
                        
  default str conv(Spec spc) = "<if (showValues) {><convValues()>;<}>";                         
  
  str actCol = "#dc3545";
  str nxtCol = "#007bff";
  str valCol = "#d6d8db";
    
  str prefix = instance == "" ? "<spc.name>" : instance;
  
  str labelAndActive(str label, str state, str ns) = "[Label=\"<label>\" color=\"<actCol>\" active]" when str total := ((ns != "") ? "<replaceAll(ns, ".", "::")>::<state>" : state), toLowerCase(total) == toLowerCase(activeState);
  default str labelAndActive(str label, str _, str _) = "[Label=\"<label>\"]";
  
  str active(str state) = "[color=\"<actCol>\" active]" when state == activeState;
  default str active(str state) = "";
  
  str checkNext(str from, set[TransEvent] events) = "[color=\"<nxtCol>\"]" when toLowerCase(from) == toLowerCase(activeState), {e | TransEvent e <- events, "<e>" == nextTrans} != {};
  default str checkNext(str from, set[TransEvent] _) = "";
  
  str convValues() = "<prefix>.vals[Label=\"Values\" color=\"<valCol>\"]:
                     '  <intercalate("\n", ["<f>: <values[f]>" | f <- values])>"
                     when values != (); 
  default str convValues() = "<prefix>.vals[Label=\"Values\" color=\"<valCol>\"] : -";

  set[str] defStates = {};
    
  str convLifeCycle((States)`states: <StateBlock root>`) 
    = "<if (/(Transition)`(*) -\> <State _>: <{TransEvent ","}+ _>;` := root) {><prefix>.initial<active("initial")>,<}> 
      '<if (/(Transition)`<State _> -\> (*): <{TransEvent ","}+ _>;` := root) {><prefix>.final<active("final")>,<}>
      '<convLifeCycle(root, "")>";
  
  str convLifeCycle((StateBlock)`<InnerStates inner> <Transition* trans>`, str ns) {
    list[str] states = [];
    
    // check whether inner state does not contain sub state, otherwise define later
    set[str] superStates = {"<super>" | (Transition)`<Id super> { <StateBlock _> }` <- trans}; 
    for (Id innerState <- inner.states, "<innerState>" notin superStates, "<innerState>" notin defStates) {
      states += "<prefix>.<if (ns != "") {><ns>.<}><innerState><labelAndActive("<innerState>", "<innerState>", ns)>";
      defStates += "<ns>.<innerState>";         
    }
    
    tuple[list[str] states, list[str] trans] other = <[],[]>;
    for (t <- trans) {
      res = convLifeCycle(t,ns);
      other.states = res<0>;
      other.trans = res<1>; 
    }
    
    return "<intercalate(",", states + other.states)>;
           '<intercalate("\n", (other.trans))>";
  }
  
  str convLifeCycle((StateBlock)`<Transition* trans>`, str ns) {
    tuple[list[str] states, list[str] trans] other = <[],[]>;
    for (t <- trans) {
      res = convLifeCycle(t, ns);
      other.states += res<0>;
      other.trans += res<1>;
    }
    
    return "<intercalate(",", other.states)>;
           '<intercalate("\n", other.trans)>";  
  }
  
  tuple[list[str], list[str]] convLifeCycle((Transition)`<State from> -\> <State to>: <{TransEvent ","}+ events>;`, str ns) {
    list[str] states = []; 
    list[str] trans = [];
    
    bool isRef((State)`<Id name>`) = "<ns>.<name>" in defStates || ".<name>" in defStates; 
    bool isRef((State)`<Id n>::<{Id "::"}+ m>`) = true; // qualified names are always references
            
    str getStateName((State)`<Id name>`)              = "<if (ns != "") {><ns>.<}><name>";        
    str getStateName((State)`<Id n>::<{Id "::"}+ m>`) = replaceAll("<n>::<m>", "::", ".");        
    
    str getTransState((State)`<Id name>`) {
      if (ns != "", "<ns>.<name>" in defStates) {
        // ref to node in current (sub) state
        return "<ns>.<name>";
      } else {
        return "<name>";
      }
    }
    str getTransState((State)`<Id n>::<{Id "::"}+ m>`) = replaceAll("<n>::<m>", "::", ".");        
    
                     
    if ("<from>" == "(*)") {
      if (!isRef(to)) {
        states += ["<prefix>.<getStateName(to)><labelAndActive("<to>","<to>", ns)>"];
        defStates += "<ns>.<to>";
      }
      
      trans += ["<prefix>.initial -\> <prefix>.<getTransState(to)><checkNext("initial", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";"];
    } else if ("<to>" == "(*)") {
      if (!isRef(from)) {
        states += ["<prefix>.<getStateName(from)><labelAndActive("<from>","<from>", ns)>"];
        defStates += "<ns>.<from>";
      }

      trans += ["<prefix>.<getTransState(from)> -\> <prefix>.final<checkNext("<from>", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";"];
    } else {
      if (!isRef(from)) {
        states += ["<prefix>.<getStateName(from)><labelAndActive("<from>","<from>", ns)>"];
        defStates += "<ns>.<from>";
      } 
      
      if (!isRef(to)) {
        states += ["<prefix>.<getStateName(to)><labelAndActive("<to>","<to>",ns)>"];
        defStates += "<ns>.<to>";
      }

      trans += ["<prefix>.<getTransState(from)> -\> <prefix>.<getTransState(to)><checkNext("<from>", {e | e <- events})>: \"  <intercalate(", ", [convEvent(e) | e <- events])>\";"];
    }                     
    
    return <states,trans>;
  }
  
  tuple[list[str], list[str]] convLifeCycle((Transition)`<Id super> { <StateBlock child> }`, str ns) {
    defStates += "<ns>.<super>";
    states = ["<prefix>.<if (ns != "") {><ns>.<}><super>[Label=\"<super>\"] {
             '  <convLifeCycle(child, ns != "" ? "<ns>.<super>" : "<super>")>
             '}"];
             
    return <states, []>;             
  }

  str convEvent((TransEvent)`empty`) = "&#949;";
  str convEvent((TransEvent)`<QualifiedName event>`) = "<event>";

  str smCatStr = conv(spc);

  return smCatStr;
}