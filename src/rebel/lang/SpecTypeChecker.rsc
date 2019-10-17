module rebel::lang::SpecTypeChecker

import rebel::lang::SpecSyntax;
import util::PathUtil;

extend rebel::lang::CommonTypeChecker;

void collect(current: (Part)`<Spec spc>`, Collector c) {
  collect(spc, c);
} 

void collect(current: (Spec)`spec <Id name> <Fields? fields> <Constraints? constraints> <Event* events> <States? states>`, Collector c) {
  c.define("<name>", specId(), current, defType(specType("<name>")));
  
  c.enterScope(current); 
       
    if (/Fields flds <- fields) {
      collect(flds.fields, c);
    }  
    
    collect(events, c);
    if (/States sts <- states) {
      collectStates(sts,c);
      collect(sts.trans, c);
    }
  
  c.leaveScope(current);
}

void collect(current: (Field)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", fieldId(), name, defType(tipe));
  collect(tipe, c);
}

void collectStates(States sts, Collector c) {
  set[State] done = {};
  
  visit(sts) {
    case (Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`: {
      if (from notin done) {
        c.define("<from>", stateId(), from, defType(stateType()));
        done += from;
      } else {
        c.use(from, {stateId()});        
      }
      
      if (to notin done) {
        c.define("<to>", stateId(), to, defType(stateType()));
        done += to;
      } else {
        c.use(to, {stateId()});
      }         
    }
    case (Transition)`<State super> <InnerStates? inner> { <Transition* trans> }`: {
      for (/InnerStates is := inner, State s <- is.states) {
        c.define("<s>", stateId(), s, defType(stateType()));
      }
    }
  }
  
  // add an 'initialized' state
  c.define("initialized", stateId(), sts, defType(stateType()));
}

void collect(current: (Transition)`<State from>-\><State to> : <{TransEvent ","}+ events>;`, Collector c) {
  // 'from' and 'to' are already done earlier
  collect(events,c);
}

void collect(current: (Transition)`<State super> <InnerStates? inner> { <Transition* trans> }`, Collector c) {
  collect(super,c);
  
  if (/InnerStates inn := inner) {
    collect(inn.states,c);   
  }
  
  collect(trans,c);
}

void collect((TransEvent)`<Id event>`, Collector c) {
  c.use(event, {eventId()});
}

void collect(current: (TransEvent)`<Id event>::<Id variant>`, Collector c) {
  c.useQualified(["<event>","<variant>"], current, {eventVariantId()}, {eventId()});
}

void collect((TransEvent)`empty`, Collector c) {}

void collect(current: (State)`<Id name>`, Collector c) {
  c.use(name, {stateId()});
}

void collect(current: (State)`(*)`, Collector c) {}

void collect(current: (Event)`<Initial? init> event <Id name>(<{FormalParam ","}* formals>) <EventBody body>`, Collector c) {
  list[Id] fp = [f.name | f <- formals];
  
  c.define("<name>", eventId(), current, defType(fp, 
    AType (Solver s) {
      return eventType(atypeList([s.getType(f) | f <- fp]));
    }));
  
  c.enterScope(current);
    c.push("eventName", "<name>");
    
    if (/(Initial)`init` := init) {
      c.setScopeInfo(c.getScope(), eventScope(), initialEvent());
    }
      
    collect(formals, body, c);

    c.pop("eventName");
    
  c.leaveScope(current);
}

void collect(current: (EventVariant)`<Outcome outcome> <Id name> <EventVariantBody body>`, Collector c) {
  c.fact(current, boolType());
  c.define("<name>", eventVariantId(), name, defType(current));
  
  c.enterScope(current); 
    collect(body, c);
  c.leaveScope(current);
}


void collect(current: (FormalParam)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", paramId(), name, defType(tipe));
  collect(tipe, c);
} 

void collect((EventBody)`<Pre? maybePre> <Post? maybePost> <EventVariant* variants>`, Collector c) {
  if (/Pre pre := maybePre) {
    c.push("phase", prePhase());
    
    for (Formula f <- pre.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");
  }
  
  if (/Post post := maybePost) {
    c.push("phase", postPhase());
  
    for (Formula f <- post.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");    
  }
  
  collect(variants, c);
}

void collect((EventVariantBody)`<Pre? maybePre> <Post? maybePost>`, Collector c) {
  if (/Pre pre := maybePre) {
    c.push("phase", prePhase());
    
    for (Formula f <- pre.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");
  }
  
  if (/Post post := maybePost) {
    c.push("phase", postPhase());
  
    for (Formula f <- post.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");    
  }
}

void collect(current: (Formula)`<Expr spc>.<Id event>(<{Expr ","}* arguments>)`, Collector c) {
  c.useViaType(spc, event, {eventId()});
  
  args = [arg | arg <- arguments];
  
  c.calculate("raise event <event>", current, event + args, 
    AType (Solver s) {
      eType = s.getType(event);
      
      if (eventType(formalTypes) := s.getType(event)) {
        argTypes = atypeList([s.getType(a) | a <- args]);
        s.requireEqual(argTypes, formalTypes, 
          error(current, "Expected arguments %t, found %t", formalTypes, argTypes)); 
      } else {
        s.report(error(current, "Event expected, found %t", eType));
      }
      
      return boolType();
    });
  
  
  collect(spc, arguments, c);
}