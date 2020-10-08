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
      c.clearStack("states_done");
      collect(sts.root, c);
      
      done = getDefStates(c);
      
      if ("$$init$$" in done) {
        c.define("initialized", stateId(), sts, defType(stateType()));
      }
      if ("$$fin$$" in done) {
        c.define("finalized", stateId(), sts, defType(stateType()));
      } 
      if ({"$$init$$", "$$fin$$"} & done != {}) {
        c.define("uninitialized", stateId(), sts, defType(stateType()));
      }
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

void collect(current: (StateBlock)`<InnerStates inner> <Transition* trans>`, Collector c) {
  for (Id state <- inner.states) { // If there are inner states, then they should always be defined
    // check if the inner state is not being used for a sub state machine
    if ((Transition)`<Id state> { <StateBlock _> }` <- trans) {
      // do nothing, will be defined later
      ;
    } 
    else {
      defineState("<state>", state, c);
    }
  }
  
  collect(trans, c);
}

void collect(current: (StateBlock)`<Transition* trans>`, Collector c) {
  collect(trans, c);
}

private set[str] getDefStates(Collector c) = (list[str] done := c.getStack("states_done")) ? toSet(done) : {};

private void definedState(str s, Collector c) {
  c.push("states_done", s);
}

private void pushStateQualifier(str q, Collector c) { c.push("state_scope", q); }
private void popStateQualifier(Collector c) { c.pop("state_scope"); }

private list[str] getStateQualifiers(Collector c) = (list[str] q := c.getStack("state_scope")) ? reverse(q) : [];

private void defineState(str state, Tree t, Collector c) {
  c.define(state, stateId(), t, defType(stateType()));
  
  list[str] sq = getStateQualifiers(c);
  if (sq != []) {
    str qn = intercalate("::", sq + [state]);
    c.define(qn, stateId(), t, defType(stateType()));
  } 
  
  definedState(state, c);
}

private bool alreadyDefinedState(str s, Collector c) = s in getDefStates(c);   

void collect(current: (Transition)`<State from>-\><State to> : <{TransEvent ","}+ events>;`, Collector c) {
  // Check if the states are already in the done list. If so, reference, otherwise add. Always reference if it concerns a fully qualified referenced state
  void collectState(State st) {
    if (st has name) {
      
      if ((QualifiedName)`<Id name>` := st.name, !alreadyDefinedState("<name>",c)) {
        defineState("<name>", st, c);
      } else {
        c.use(st, {stateId()});
      }
    } 
  }
  
  if ("<from>" == "(*)") {
    definedState("$$init$$", c);
  } else{  
    collectState(from); 
  }
    
  if ("<to>" == "(*)") {
    definedState("$$fin$$", c);
  } else { 
    collectState(to); 
  }
  
  collect(events,c);
}

void collect(current: (Transition)`<Id super> { <StateBlock child> }`, Collector c) {
  defineState("<super>", current, c);
  
  //c.enterScope(current); 
    pushStateQualifier("<super>", c);
    collect(child, c);
    popStateQualifier(c);
  //c.leaveScope(current);
}

void collect(current: (TransEvent)`<QualifiedName event>`, Collector c) {
  //if ((QualifiedName)`<Id ev>` := event) {
    c.use(event, {eventId(),eventVariantId()});
  //} else {
    //c.useQualified(["<e>" | e <- event.names], event, {eventId(), eventVariantId()}, {eventId()});
  //}  
}

void collect((TransEvent)`empty`, Collector c) {}

void collect(current: (Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* formals>) <EventBody body>`, Collector c) {
  list[Id] fp = [f.name | f <- formals];

  ModifierInfo toModInfo((Modifier)`init`) = initial();
  ModifierInfo toModInfo((Modifier)`final`) = final();
  ModifierInfo toModInfo((Modifier)`internal`) = internal();
  
  set[ModifierInfo] mods = {toModInfo(m) | Modifier m <- modifiers};
  
  c.define("<name>", eventId(), current, defType(fp, 
    AType (Solver s) {
      return eventType(namedTypeList([<"<f>",s.getType(f)> | f <- fp]), mods);
    })); 
  
  // Scan for possible variants, also define here to cicumvent qualified naming with external types issue
  for (EventVariant var <- body.variants) {
    c.define("<name>::<var.name>", eventVariantId(), var, defType(fp, 
      AType (Solver s) {
        return eventType(namedTypeList([<"<f>",s.getType(f)> | f <- fp]), mods);
      }));
  }
  
  c.enterScope(current);
    c.push("eventName", "<name>");
    
    //if (/(Modifier)`init` := modifiers) {
    //  c.setScopeInfo(c.getScope(), eventScope(), initial());
    //} else if (/(Modifier)`final` := modifiers) {
    //  c.setScopeInfo(c.getScope(), eventScope(), final());
    //}    
      
    collect(formals, body, c);

    c.pop("eventName");
    
  c.leaveScope(current);
}

void collect(current: (EventVariant)`variant <Id name> <EventVariantBody body>`, Collector c) {
  c.fact(current, boolType());
  //c.define("<name>", eventVariantId(), current, defType(current));
  // double define to workaround 'type qualification' problem
  
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

void collect(current: (Formula)`<Expr spc>.<QualifiedName event>(<{Expr ","}* arguments>)`, Collector c) {
  c.useViaType(spc, event, {eventId(),eventVariantId(),predId()});
  
  args = [arg | arg <- arguments];
  
  c.calculate("raise event <event>", current, event + args, 
    AType (Solver s) {
      eType = s.getType(event);
      
      if (eventType(namedTypeList(ntl),_) := s.getType(event) || predType(namedTypeList(ntl)) := s.getType(event)) {
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
