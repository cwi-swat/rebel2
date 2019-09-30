module analysis::Normalizer

import lang::Syntax;

import ParseTree;
import List;
import String;
import IO;

// Test imports
import lang::Parser;

Module normalizeCoffeeMachine() = normalize(parseModule(|project://rebel2/examples/CoffeeMachine.rebel|)); 

Module normalize(Module m, bool saveOutput = true) {
  m.spc = normalize(m.spc, saveOutput);
  return m;
}

Spec normalize(Spec spc, bool saveOutput) {
  set[str] fields = {"<f.name>" | /Field f := spc};
  
  list[Event] normEvents = normalizeEvents([e | Event e <- spc.events]);
  normEvents = addFrameConditions(fields, normEvents);
  normEvents = addEmptyTransitionIfNecessary(spc, normEvents);
  
  spc.events = buildNormEvents(normEvents);
  spc.states = normalizeStates(spc.states);
  spc = addImplicitMultiplicities(spc);
  
  if (saveOutput) {
    writeFile(|project://rebel2/examples/latest-normalized-spc.rebel|, spc);
  }
  
  return spc;
}

Spec addImplicitMultiplicities(Spec spc) 
  = visit (spc) {
    case (Type)`<TypeName tp>` => (Type)`one <TypeName tp>`
  };

list[Event] addFrameConditions(set[str] fields, list[Event] events) {
  list[Event] framedEvents = [];

  for (e <- events) {
     e.body.post = addFrameConditions(fields, e.body.post, "<e.name>");
     framedEvents += e;
  }
  
  return framedEvents;
}

list[Event] normalizeEvents(list[Event] events) {
  for (Event e <- events) {
    bool changed = false;
    
    list[Event] addedEvents = [];
    
    for (EventVariant ev <- e.body.variants) {
      changed = true;
      
      addedEvents += normalizeVariant(ev, e);
    }
    
    if (changed) {
      // remove variants;
      events -= e;
      
      e.body = buildEventBody(e.body.pre, e.body.post);
      
      events += e;
      events += addedEvents;      
    }
  }
  
  return events;
}

private list[Event] addEmptyTransitionIfNecessary(Spec spc, list[Event] events) {
  if (/(TransEvent)`empty` := spc.states) {
    events += (Event)`event empty()
                     '`;
  }
  
  return events;
}

private EventBody buildEventBody(Pre? origPre, Post? origPost) {
  Pre pre = emptyPre();
  Post post = emptyPost();
 
  if (/Pre pr := origPre) {
    pre = pr;
  }
  if (/Post ps := origPost) {
    post = ps;
  }  
  
  return (EventBody)`<Pre pre> 
                    '<Post post>
                    '
                    '`;
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
     tmp = (Event)`event foo() 
                  'post:
                  '  <Formula frameCond>,  // Frame condition
                  '  <{Formula ","}* formulas>;
                  '`;
  } else {
     tmp = (Event)`event foo() 
                  'post:
                  '  <Formula frameCond>; // Frame condition
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
  var.name = [Id]"<e.name>_<ev.name>";
  
  var.body = buildEventBody(ev.body.pre, ev.body.post);
  
  return var; 
}
            
private Event* buildNormEvents(list[Event] es) {
  Spec s = (Spec)`spec foo`;
  
  for (Event e <- es, (Spec)`spec foo <Event* es2>` := s) {
    s = (Spec)`spec foo 
              '<Event* es2> 
              '<Event e>
              '`;
  }
  
  return s.events;
}

private States? normalizeStates(States? states) {
  states = normalizeInnerStates(states);
  
  rel[str super, str inner] mapping = {<"<super>", "<n>"> | /(Transition)`<State super> <InnerStates inner> { <Transition* trans> }` := states, State n <- inner.states};

  rel[str from, str to, str events] normalized = {};

  visit(states) {
    case (Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`: {
      
      bool mapped = false;
      for (<"<from>", str inner> <- mapping) {
        mapped = true;
        normalized += <inner, "<to>", "<events>">;
      }
      
      if (!mapped) {
        normalized += <"<from>", "<to>", "<events>">;
      } 
    }
  }
  
  Spec foo = [Spec]trim("spec foo 
                        'states : 
                        '<for (n <- normalized) {>  <n.from> -\> <n.to> : <n.events>;
                        '<}>");
                 
  return foo.states;
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
