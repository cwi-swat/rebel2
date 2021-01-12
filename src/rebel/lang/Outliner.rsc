module rebel::lang::Outliner

import rebel::lang::Syntax;
import util::IDE;

import ParseTree;
import Map;
import List;
import Set;

data RebelOutline(loc location = |unknown:///|)
  = spec(str name, list[RebelOutline] fields, list[RebelOutline] events, set[RebelOutline] states, list[RebelOutline] assumptions)
  | field(str name, str tipe)
  | event(str name, list[RebelOutline] params)
  | state(str name)
  | assumption(str name)
  | param(str name, str tipe)
  | assertion(str name)
  | config(str name)
  | run(str name)
  | check(str name)
  ;

node buildOutline(Module m) {
  map[loc,RebelOutline] specs = ();
  
  list[RebelOutline] assertions = [];
  list[RebelOutline] configs = [];
  list[RebelOutline] commands = [];
  
  loc current = |unknown:///|;
  top-down visit(m) {
    case Spec s:  {
      current = s@\loc;
      specs[current] = spec("<s.name>", [], [], {}, [], location = s@\loc);
    }
    case Field f: specs[current].fields += [field("<f.name>", "<f.tipe>", location = f@\loc)];
    case Event e: specs[current].events += [event("<e.name>", [param("<p.name>", "<p.tipe>") | p <- e.params], location = e@\loc)];
    //case State s: {
    //  if ("<s>" != "(*)") {
    //    specs[current].states += {state("<s.name>", location=s@\loc)};
    //  }
    //}
    case Fact f: specs[current].assumptions += [assumption("<f.name>", location=f@\loc)];
    case Assert a: assertions += [assertion("<a.name>", location=a@\loc)];
    case Config c: configs += [config("<c.name>", location=c@\loc)];
    case Check c: commands += ["<c.cmd>" == "run" ? run("<c.name>", location=c@\loc) : check("<c.name>", location=c@\loc)];
  }
  
  return "outline"(
    ["Specifications (<size(specs)>)"([
      "spec"(
        ["Fields (<size(specs[s].fields)>)"(["field"()[@\loc=f.location][@label="<f.name> : <f.tipe>"] | f <- specs[s].fields])] +
        ["Events (<size(specs[s].events)>)"(["event"()[@\loc=e.location][@label="<e.name> (<intercalate(",", ["<p.name> : <p.tipe>" | p <- e.params])>)"] | e <- specs[s].events])] +
        ["Assumptions (<size(specs[s].assumptions)>)"(["assumption"()[@\loc=a.location][@label="<a.name>"] | a <- specs[s].assumptions])] 
        //["States (<size(specs[s].states)>)"(["state"([])[@\loc=st.location][@label="<st.name>"] | st <- specs[s].states])] +
       )[@label=specs[s].name][@\loc=specs[s].location] | s <- specs])] +
    ["Assertions (<size(assertions)>)"(["assert"()[@\loc=a.location][@label=a.name] | a <- assertions])] +
    ["Configs (<size(configs)>)"(["config"()[@\loc=c.location][@label=c.name] | c <- configs])] +
    ["Commands (<size(commands)>)"(["command"()[@\loc=c.location][@label=label] | c <- commands, str label := ((run(_) := c) ? "run <c.name>" : "check <c.name>")])]    
  );
}