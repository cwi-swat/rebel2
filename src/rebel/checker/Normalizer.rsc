module rebel::checker::Normalizer

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;
import rebel::lang::Parser;

import util::PathUtil;
import util::Benchmark;

import ParseTree;
import List;
import Set;
import String;
import IO; 
import Location;

alias NormalizedModule = tuple[Module m, TModel tm, int duration];

NormalizedModule normalizeAndTypeCheck(Module origMod, TModel origTm, PathConfig pcfg, bool saveNormalizedMod = false) {
  print("Normalizing prepared module ...");
  int startTime = cpuTime();

  Module normMod = normalizeEventVariantSyncs(origMod, origTm);
  normMod = normalizeStateQueries(normMod, origTm);
  
  normMod = visit(normMod) {
    case (Part)`<Spec spc>` => (Part)`<Spec nSpc>` when Spec nSpc := normalize(spc, origTm)
  }
 
  if (saveNormalizedMod) {
    writeFile(addModuleToBase(pcfg.checks, normMod)[extension="norm.rebel"], normMod);
  }
  
  // TEMP / TODO: Cop-out for Type checking issues with generated code (without reparsing). Location trouble on generated nodes
  normMod = parse(#Module, "<normMod>");
  ////////////////
    
  TModel normModTm = rebelTModelFromModule(normMod, {}, pcfg, debug = false);
  
  int duration = (cpuTime() - startTime) / 1000000;
  
  println("done, took: <duration> ms.");
  
  return <normMod, normModTm, duration>;
}

Spec normalize(Spec spc, TModel origTm) {
  set[str] fields = {"<f.name>" | /Field f := spc};
  
  list[Event] normEvents = [e | Event e <- spc.events];

  normEvents = addEmptyTransitionIfNecessary(spc, normEvents);
  normEvents = normalizeEventVariants(normEvents, origTm);
  normEvents = addFrameConditionsToEvents(fields, normEvents);
  if (fields != {} || /Transition _ := spc.states){
    normEvents += createFrameEvent(spc);
  }
  
  spc.events = buildNormEvents(normEvents);
  spc.states = normalizeStates(spc.states, origTm);

  return spc;
}

Module normalizeStateQueries(Module m, TModel origTm) {
  rel[loc, Define] definitions = {<d.defined, d> | d <- origTm.defines, d.idRole == stateId()};
  rel[loc, str] substates = {<def, child> | loc def <- definitions<0>, str child <- findChildrenTransitive(def, definitions)};
  
  set[str] findSubStates(loc use) {
    if ({loc def} := origTm.useDef[use]) {
      return substates[def];  
    }
    
    throw "Unable to find state referenced at `<use>`";
  }
  
  Formula normStateQuery(orig:(Formula)`<Expr expr> is <QualifiedName state>`) {
    if (set[str] substates := findSubStates(state@\loc), substates != {}) {
      return buildDisj(expr, substates);
    } else if (contains("<state>", "::")) {
      return [Formula]"<expr> is <replaceAll("<state>", "::", "__")>";
    } else {
      return orig;
    }
  }
  Formula buildDisj(Expr expr, set[str] substates) = [Formula]"(<intercalate(" || ", ["<expr> is <replaceAll(sub, "::", "__")>" | sub <- substates])>)"; 
  
  return visit(m) {
    case orig:(Formula)`<Expr expr> is <QualifiedName state>` => normStateQuery(orig)
  }
}

private set[str] findChildrenTransitive(loc super, rel[loc, Define] definitions) {
  set[str] children = {};
  for (<loc def, Define d> <- definitions, def != super, isContainedIn(def, super), contains(d.id, "::")) {
    children += d.id;  
  }  
  return children;
}

Module normalizeEventVariantSyncs(Module m, TModel origTm) {
  set[Define] variants = {d | Define d <- origTm.definitions<1>, d.idRole == eventVariantId()}; //, /.*[:][:].*/ !:= d.id};
  set[Define] findVariants(loc eventRef) = {v | v <- variants, isStrictlyContainedIn(v.defined, eventDef)} when {loc eventDef} := origTm.useDef[eventRef]; 
  default set[Define] findVariants(loc eventRef) = {};  

  Formula buildSyncDisj((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, set[Define] variants) 
    = buildFormDisj([(Formula)`<Expr spc>.<Id eventVar>(<{Expr ","}* params>)` | Define var <- variants, Id eventVar := [Id]"<replaceAll(var.id, "::", "__")>"]); 

  Formula buildRaisedDisj((Formula)`<Id event> on <Expr spc> <WithAssignments? as>`, set[Define] variants)
    = buildFormDisj([(Formula)`<Id eventVar> on <Expr spc> <WithAssignments? as>` | Define var <- variants, Id eventVar := [Id]"<replaceAll(var.id, "::", "__")>"]);

  Formula buildFormDisj(list[Formula] terms) = [Formula]"(<intercalate(" || ", terms)>)";
  
  Transition rewriteVariants(Transition orig) {
    set[str] result = {};
    bool rewritten = false;

    for (e <- orig.events) {
      vars = findVariants(e@\loc);

      if (vars != {}) {
        result += {replaceAll(ev.id, "::", "__") | Define ev <- vars};
        rewritten = true;
      } else {
        result += "<e>";
      }
    }
    
    if (!rewritten) {
      return orig;
    } else {
      Transition temp = [Transition]"a -\> b: <intercalate(",", ["<e>" | e <- result])>;";
      orig.events = temp.events;
      return orig;
    }
  }
  
  return visit(m) {
    // Raising an event with variants. Must be one of the variants
    case orig:(Formula)`<Expr _>.<Id event>(<{Expr ","}* _>)` => buildSyncDisj(orig, vars) 
      when set[Define] vars := findVariants(event@\loc), vars != {}     

    case orig:(Formula)`<Id evnt> on <Expr _> <WithAssignments? _>` => buildRaisedDisj(orig, vars) 
      when set[Define] vars := findVariants(evnt@\loc), vars != {}     
      
    // Raising an event variant directly. Make sure to reference the normalized event variant (renaming)
    case orig:(Formula)`<Expr exp>.<Id event>::<Id var>(<{Expr ","}* args>)` => (Formula)`<Expr exp>.<Id eventVar>(<{Expr ","}* args>)`
      when Id eventVar := [Id]"<event>__<var>"
      
    case orig:(Formula)`<Id event>::<Id var> on <Expr spc> <WithAssignments? as>` => (Formula)`<Id eventVar> on <Expr spc> <WithAssignments? as>`
      when Id eventVar := [Id]"<event>__<var>"      
      
    case orig:(Transition)`<State from> -\> <State to>: <{TransEvent ","}+ events>;` => t 
      when Transition t := rewriteVariants(orig)
  } 
}

Event createFrameEvent(Spec spc) {
  str frameCond = "<intercalate(",\n", ["this.<f.name>\' = this.<f.name>" | /Field f <- spc.fields])>";
                  
  return [Event]"internal event __frame() 
                '  <if (frameCond != "") {>  post: <frameCond>;<}>
                '";                  
}

list[Event] addFrameConditionsToEvents(set[str] fields, list[Event] events) {
  list[Event] framedEvents = [];

  for (e <- events) {
     if (/(Modifier)`init` !:= e.modifiers, /(Modifier)`final` !:= e.modifiers) {
      e.body.post = addFrameConditions(fields, e.body.post, "<e.name>");
     }
     
     framedEvents += e;
  }
  
  return framedEvents;
}

list[Event] normalizeEventVariants(list[Event] events, TModel origTm) {
  Event normVar(EventVariant ev, Event e) {
    Event var = e;
    var.name = [Id]"<e.name>__<ev.name>";
  
    var.body = buildEventBody(mergePreConditions(e,ev).pre, mergePostConditions(e,ev).post);
  
    return var; 
  }

  list[Event] checkForVariantDefs(Event e) = [normVar(ev, e) | EventVariant ev <- e.body.variants];

  for (Event e <- events) {
    list[Event] varEvents = checkForVariantDefs(e);
    if (varEvents != []) {
      events -= e;
      events += varEvents;
    } 
  }
  
  return events;
}

private list[Event] addEmptyTransitionIfNecessary(Spec spc, list[Event] events) {
  if (/(TransEvent)`empty` := spc.states) {
    events += (Event)`  event empty()
                     '`;
  }
  
  return events;
}

private EventBody mergePreConditions(Event orig, EventVariant var) {
  Event addPreCond(Event tmp, Formula f) {
    if (/(Pre)`pre: <{Formula ","}* formulas>;` := tmp.body.pre) {
      return (Event)`  event foo() 
                    '    pre:
                    '      <Formula f>,
                    '      <{Formula ","}* formulas>;
                    '`;
    } else {
      return (Event)`  event foo() 
                    '    pre:
                    '      <Formula f>;
                    '`;
    }
  
  }

  for (/(Pre)`pre: <{Formula ","}* formulas>;` := var.body.pre, Formula f <- formulas) {
    orig = addPreCond(orig, f);
  } 
  
  return orig.body;
}

private EventBody mergePostConditions(Event orig, EventVariant var) {
  Event addPostCond(Event tmp, Formula f) {
    if (/(Post)`post: <{Formula ","}* formulas>;` := tmp.body.post) {
      return (Event)`  event foo() 
                    '    post:
                    '      <Formula f>,
                    '      <{Formula ","}* formulas>;
                    '`;
    } else {
      return (Event)`  event foo() 
                    '    post:
                    '      <Formula f>;
                    '`;
    }
  
  }

  for (/(Post)`post: <{Formula ","}* formulas>;` := var.body.post, Formula f <- formulas) {
    orig = addPostCond(orig, f);
  } 
  
  return orig.body;
}


private EventBody buildEventBody(Pre? origPre, Post? origPost) {
  return [EventBody]"<origPre> 
                    '<origPost>
                    '";
}

private Post? addFrameConditions(set[str] fields, Post? post, str eventName) {
  set[str] referencedPostVals = {"<name>" | /(Expr)`this.<Id name>'` <- post}; 

  list[Formula] frameConditions = [];

  for (f <- fields) {
    // If the post value of a field is not referenced, frame it
    if (f notin referencedPostVals) {
      Id fieldName = [Id]"<f>";
      frameConditions += (Formula)`this.<Id fieldName>' = this.<Id fieldName>`;
    }
  }
  
  if (frameConditions == []) {
    return post;
  } else {
    post = buildFrameConditions(post, frameConditions);
    return post;
  }  
}

private Post? buildFrameConditions(Post? p, list[Formula] frameCond) {
  Event tmp;
  
  for (Formula fc <- frameCond) {
    if (/(Post)`post: <{Formula ","}* formulas>;` := p) {
       tmp = (Event)`  event foo() 
                    '    post:
                    '      <Formula fc>, // Frame condition
                    '      <{Formula ","}* formulas>;
                    '`;
    } else {
       tmp = (Event)`  event foo() 
                    '    post:
                    '      <Formula fc>; // Frame condition 
                    '`;
    }
    
    p = tmp.body.post;
  }
    
  return tmp.body.post;
}

@memo
private Pre emptyPre() = (Pre)`pre: ;`;
@memo
private Post emptyPost() = (Post)`post: ;`;
            
private Event* buildNormEvents(list[Event] es) {
  Spec s = (Spec)`spec foo`;
  
  for (Event e <- es, (Spec)`spec foo <Event* es2>` := s) {
    s = (Spec)`spec foo 
              '  <Event* es2> 
              '  <Event e>
              '`;
  }
  
  return s.events;
}

private States? normalizeStates(States? states, TModel tm) {
  if (/States _ !:= states) {
    return states;
  }
  
  rel[loc, Define] definitions = {<d.defined, d> | d <- tm.defines, d.idRole == stateId()};
    
  str getQualifiedName(loc use) {
    loc stateDefLoc = {loc def} := tm.useDef[use] ? def : use;
    set[Define] defs = definitions[stateDefLoc];

    if ({Define d} := defs) {
      return replaceAll(d.id, "::", "__");
    } else {
      for (Define d <- defs, contains(d.id, "::")) {
        return replaceAll(d.id, "::", "__");
      }
    }
    
    throw "Unable to find qualified state id for `<use>`";
  }

  rel[str super, str transChild] substates = {<qnSuper, child> | /t:(Transition)`<Id _> { <StateBlock block> }` := states, 
    str qnSuper := getQualifiedName(t@\loc), child <- findChildrenTransitive(block@\loc, definitions)};
  // remove all the states that are super states themselfs
  substates -= substates<1,0>;   

  lrel[str from, str to, str event] normalized = [];

  visit(states) {
    case t:(Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`: {
      list[str] evnts = [normalizeEventRefs(e) | e <- events];
      str t = "<to>" == "(*)" ? "<to>" : getQualifiedName(to@\loc);
      str f = "<from>" == "(*)" ? "<from>" : getQualifiedName(from@\loc);
      
      if (substates[f] != {}) {
        normalized += [<replaceAll(c, "::", "__"),t,e> | str c <- substates[f], e <- evnts];
      } else {  
        normalized += [<f,t,e> | e <- evnts];
      }      
    }
  }
    
  Spec foo = parse(#Spec, trim("spec foo 
                          'states: 
                          '<for (n <- normalized) {>  <n.from> -\> <n.to> : <n.event>;
                          <}>"));
                 
  return foo.states;
}

private str normalizeEventRefs((TransEvent)`<Id event>::<Id variant>`) = "<event>__<variant>";
private str normalizeEventRefs(ev:(TransEvent)`<Id event>`) = "<ev>";
private str normalizeEventRefs(ev:(TransEvent)`empty`) = "empty";

private States? normalizeInnerStates(States? states) {
  states = visit(states) {
    case (Transition)`<State super> { <Transition* trans> }` 
      => (Transition)`<State super> <InnerStates inner> { <Transition* trans> }`
      when 
        InnerStates inner := [InnerStates]"[<intercalate(",", dup(["<s>" | /State s := trans, "<s>" != "(*)"]))>]"
  }
  
  return states;
}
