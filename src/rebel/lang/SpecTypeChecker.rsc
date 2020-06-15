module rebel::lang::SpecTypeChecker

import rebel::lang::CommonSyntax;
import rebel::lang::SpecSyntax;

import util::PathUtil;
import util::Maybe;

extend analysis::typepal::TypePal;

data ScopeInfo
  = specInfo(str name)
  ;

void collect(current: (Part)`<Spec spc>`, Collector c) {
  collect(spc, c);
}  
 
Maybe[AType] getCurrentSpecType(Collector c) {
  inf = c.getScopeInfo(specScope());
  
  for (<scope,scopeInfo> <- inf, specInfo(str name) := scopeInfo) {
    return just(specType(name));
  }
  
  return nothing();
} 
 
void collect(current: (Spec)`spec <Id name> <Instances? instances> <Fields? fields> <Constraints? constraints> <Event* events> <Pred* preds> <Fact* facts> <States? states>`, Collector c) {
  c.define("<name>", specId(), current, defType(specType("<name>")));
  
  c.enterScope(current); 
    c.define("this", specId(), current, defType(specType("<name>")));
    c.setScopeInfo(c.getScope(), specScope(), specInfo("<name>"));
    
    for (/Id instance <- instances) {
      c.define("<instance>", specInstanceId(), instance, defType(specType("<name>")));
    } 
           
    if (/Fields flds <- fields) {
      collect(flds.fields, c);
    }  
    
    collect(events, c);
    if (/States sts <- states) {
      collectStates(sts,c);
      collect(sts.trans, c);
    }

    collect(facts, c);
    collect(preds, c);
        
  c.leaveScope(current);
}

void collect(current: (Field)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", fieldId(), name, defType(tipe));
  collect(tipe, c);
}

void collect(current:(Fact)`fact <Id name> = <Formula form>;`, Collector c) {
  c.define("<name>", factId(), current, defType(factType()));
  
  c.enterScope(current); 
    collect(form, c);
  c.leaveScope(current);    
}

void collect(current:(Pred)`pred <Id name> (<{FormalParam ","}* formals>) = <Formula form>;`, Collector c) {
  list[Id] fp = [f.name | f <- formals];
  
  c.define("<name>", predId(), current, defType(fp, 
    AType (Solver s) {
      return predType(namedTypeList([<"<f>",s.getType(f)> | f <- fp]));
    }));
    
  c.enterScope(current);
    collect(formals, form, c);
  c.leaveScope(current);    
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
        if (s notin done) { 
          c.define("<s>", stateId(), s, defType(stateType()));
          done += s;
        } else {
          c.use(s, {stateId()});
        }
      }
    }
  }
  
  // add an 'initialized' and 'uninitialized' state
  c.define("initialized", stateId(), sts, defType(stateType()));
  c.define("uninitialized", stateId(), sts, defType(stateType()));
  c.define("finalized", stateId(), sts, defType(stateType()));
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

void collect(current: (Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* formals>) <EventBody body>`, Collector c) {
  list[Id] fp = [f.name | f <- formals];
  
  c.define("<name>", eventId(), current, defType(fp, 
    AType (Solver s) {
      return eventType(namedTypeList([<"<f>",s.getType(f)> | f <- fp]));
    }));
  
  c.enterScope(current);
    c.push("eventName", "<name>");
    
    if (/(Modifier)`init` := modifiers) {
      c.setScopeInfo(c.getScope(), eventScope(), initialEvent());
    } else if (/(Modifier)`final` := modifiers) {
      c.setScopeInfo(c.getScope(), eventScope(), finalEvent());
    }    
      
    collect(formals, body, c);

    c.pop("eventName");
    
  c.leaveScope(current);
}

void collect(current: (EventVariant)`variant <Id name> <EventVariantBody body>`, Collector c) {
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
  c.useViaType(spc, event, {eventId(),predId()});
  
  args = [arg | arg <- arguments];
  
  c.calculate("raise event <event>", current, event + args, 
    AType (Solver s) {
      eType = s.getType(event);
      
      if (eventType(namedTypeList(ntl)) := s.getType(event) || predType(namedTypeList(ntl)) := s.getType(event)) {
        AType formalTypes = atypeList([tipe | <str _, AType tipe> <- ntl]);
        
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

void collect(current: (Lit)`this`, Collector c) {
  c.use(current, {specId()});
}
