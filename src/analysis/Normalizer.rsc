module analysis::Normalizer

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import util::PathUtil;

import ParseTree;
import List;
import Set;
import String;
import IO;
import Location;

loc normalize(Module m, TModel origTm) {
  m = normalizeEventVariantSyncs(m, origTm);

  m = visit(m) {
    case (Part)`<Spec spc>` => (Part)`<Spec nSpc>` when Spec nSpc := normalize(spc, origTm)
  }
  
  loc normPath = addModuleToBase(project(m@\loc.top) + "bin/normalized/", m);

  makeDirRecursively(normPath.parent); 

  writeFile(normPath[extension = "rebel"], m);

  return normPath[extension = "rebel"];
}

Spec normalize(Spec spc, TModel origTm) {
  set[str] fields = {"<f.name>" | /Field f := spc};
  
  list[Event] normEvents = [e | Event e <- spc.events];
  normEvents = addEmptyTransitionIfNecessary(spc, normEvents);
  normEvents = normalizeEvents(normEvents, origTm);
  normEvents = addFrameConditions(fields, normEvents);
  if (fields != {} || /Transition _ := spc.states){
    normEvents += createFrameEvent(spc);
  }
  
  spc.events = buildNormEvents(normEvents);
  spc.states = normalizeStates(spc.states);

  return spc;
}

Module normalizeEventVariantSyncs(Module m, TModel origTm) {
  set[Define] variants = {d | Define d <- origTm.definitions<1>, d.idRole == eventVariantId()};
  set[Define] findVariants(loc eventRef) = {v | v <- variants, isContainedIn(v.defined, eventDef)} when {loc eventDef} := origTm.useDef[eventRef]; 
  default set[Define] findVariants(loc eventRef) = {};  

  Formula buildSyncDisj(orig:(Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, set[Define] variants) 
    = buildFormDisj([(Formula)`<Expr spc>.<Id varId>(<{Expr ","}* params>)` | Define var <- variants, Id varId := [Id]"<event>__<var.id>"]); 

  Formula buildRaisedDisj(orig:(Formula)`<TransEvent evnt> on <Expr spc> <WithAssignments? as>`, set[Define] variants)
    = buildFormDisj([(Formula)`<TransEvent varEvnt> on <Expr spc> <WithAssignments? as>` | Define var <- variants, TransEvent varEvnt := [TransEvent]"<evnt>__<var.id>"]);

  Formula buildFormDisj(list[Formula] terms) = [Formula]"(<intercalate(" || ", terms)>)";
  
  return visit(m) {
    case orig:(Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)` => buildSyncDisj(orig, vars) 
      when set[Define] vars := findVariants(event@\loc), vars != {}     

    case orig:(Formula)`<TransEvent evnt> on <Expr spc> <WithAssignments? as>` => buildRaisedDisj(orig, vars) 
      when set[Define] vars := findVariants(evnt@\loc), vars != {}     

  } 
}

Event createFrameEvent(Spec spc) {
  str frameCond = "<intercalate(",\n", ["this.<f.name>\' = this.<f.name>" | /Field f <- spc.fields])>";
                  
  return [Event]"internal event __frame() 
                '  <if (frameCond != "") {>  post: <frameCond>;<}>
                '";                  
}

list[Event] addFrameConditions(set[str] fields, list[Event] events) {
  list[Event] framedEvents = [];

  for (e <- events) {
     e.body.post = addFrameConditions(fields, e.body.post, "<e.name>");
     framedEvents += e;
  }
  
  return framedEvents;
}

list[Event] normalizeEvents(list[Event] events, TModel origTm) {
  //set[Define] variants = {d | Define d <- origTm.definitions<1>, d.idRole == eventVariantId()};
  //set[Define] findVariants(loc eventRef) = {v | v <- variants, isContainedIn(v.defined, eventDef)}
  //  when {loc eventDef} := origTm.useDef[eventRef]; 
  //    
  //Formula buildSyncDisj(orig:(Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, set[Define] variants) 
  //  = buildFormDisj([(Formula)`<Expr spc>.<Id varId>(<{Expr ","}* params>)` | Define var <- variants, Id varId := [Id]"<event>__<var.id>"]); 
  //
  //Formula buildFormDisj(list[Formula] terms) = [Formula]"(<intercalate(" || ", terms)>)"; 
  
  list[Event] checkForVariantDefs(Event e) = [normalizeVariant(ev, e) | EventVariant ev <- e.body.variants];
   
  //Event checkForVariantSyncs(Event e) 
  //  = visit(e) {
  //      case orig:(Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)` => buildSyncDisj(orig, vars) 
  //        when set[Define] vars := findVariants(event@\loc), vars != {} 
  //    };  
  //
  //for (Event e <- events) {
  //  Event changed = checkForVariantSyncs(e);
  //  if (changed != e) {
  //    events -= e;
  //    events += changed;        
  //  }
  //}

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

  for (f <- fields) {
    // If the post value of a field is not referenced, frame it
    if (f notin referencedPostVals) {
      Id fieldName = [Id]"<f>";
      Formula frameCond = (Formula)`this.<Id fieldName>' = this.<Id fieldName>`;
      post = addFrameCondition(post, frameCond);
    }
  }
  
  return post;  
}

private Post? addFrameCondition(Post? p, Formula frameCond) {
  Event tmp;
  if (/(Post)`post: <{Formula ","}* formulas>;` := p) {
     tmp = (Event)`  event foo() 
                  '    post:
                  '      <Formula frameCond>,  // Frame condition
                  '      <{Formula ","}* formulas>;
                  '`;
  } else {
     tmp = (Event)`  event foo() 
                  '    post:
                  '      <Formula frameCond>; // Frame condition
                  '`;
  }
  
  return tmp.body.post;
}

@memo
private Pre emptyPre() = (Pre)`pre: ;`;
@memo
private Post emptyPost() = (Post)`post: ;`;

private Event normalizeVariant(EventVariant ev, Event e) {
  Event var = e;
  var.name = [Id]"<e.name>__<ev.name>";
  
  var.body = buildEventBody(mergePreConditions(e,ev).pre, mergePostConditions(e,ev).post);
  
  return var; 
}
            
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

private States? normalizeStates(States? states) {
  if (/States sts !:= states) {
    return states;
  }
  
  states = normalizeInnerStates(states);
  
  lrel[str super, str inner] mapping = [<"<super>", "<n>"> | /(Transition)`<State super> <InnerStates inner> { <Transition* trans> }` := states, State n <- inner.states];

  lrel[str from, str to, str events] normalized = [];

  visit(states) {
    case t:(Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`: {   
      te = normalizeEventRefs(t);
      
      bool mapped = false;
      for (<"<from>", str inner> <- mapping) {
        mapped = true;
        normalized += <inner, "<to>", "<te.events>">;
      }
      
      if (!mapped) {
        normalized += <"<from>", "<to>", "<te.events>">;
      } 
    }
  }
  
  Spec foo = parse(#Spec, trim("spec foo 
                          'states: 
                          '<for (n <- normalized) {>  <n.from> -\> <n.to> : <n.events>;
                          <}>"));
                 
  return foo.states;
}

private Transition normalizeEventRefs(Transition t) {
  return visit (t) {
    case (TransEvent)`<Id event>::<Id variant>` => [TransEvent]"<event>__<variant>"
  }
}

private States? normalizeInnerStates(States? states) {
  states = visit(states) {
    case (Transition)`<State super> { <Transition* trans> }` 
      => (Transition)`<State super> <InnerStates inner> { <Transition* trans> }`
      when 
        InnerStates inner := [InnerStates]"[<intercalate(",", dup(["<s>" | /State s := trans, "<s>" != "(*)"]))>]"
  }
  
  return states;
}
