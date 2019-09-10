module analysis::Checker

import analysis::DefAndUseBuilder;
import lang::Syntax;
import lang::Parser;

import Message;
import ParseTree;

set[Message] testChecker() = check(spc,buildUseDefRel(spc))
  when Spec spc := parseSpec(|project://rebel2/examples/pingpong.rebel|);

set[Message] check(Spec spc, UseDef useDef) 
  = checkEvents(spc, useDef);

set[Message] checkEvents(Spec spc, UseDef useDef) { 
  set[Message] errors = {};
  
  for (Event ev <- spc.events) {
    for (/Pre pre := ev, f <- pre.formulas) {
      errors += checkUndeclaredFieldUsage(f, useDef) 
              + checkUndeclaredParamUsage(f, useDef) 
              + checkPostNotReferencedInPre(f);
    }
    for (/Post post := ev, f <- post.formulas) {
      errors += checkUndeclaredFieldUsage(f, useDef) 
              + checkUndeclaredParamUsage(f, useDef) 
              + checkPostStateNotReferencedInPostcondition(f);
    }
  } 
  
  return errors;
}

set[Message] checkUndeclaredFieldUsage(Formula form, UseDef useDef) 
  = {error("Undeclared field", e@\loc) | /e:(Expr)`this.<Id field>` := form, useDef[e@\loc] == {}};

set[Message] checkUndeclaredParamUsage(Formula form, UseDef useDef)
  = {error("Undeclared parameter", e@\loc) | /e:(Expr)`<Id param>` := form, useDef[e@\loc] == {}};

set[Message] checkPostNotReferencedInPre(Formula form) 
  = {error("Can not reference post state in precondition", e@\loc) | /e:(Expr)`<Expr _>'` := form};

set[Message] checkPostStateNotReferencedInPostcondition(Formula form) 
  = {warning("Post state is not referenced, have you forgotten the \' or should this be a precondition?", form@\loc) | /(Expr)`<Expr _>'` !:= form};  