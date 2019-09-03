module analysis::Checker

import analysis::DefAndUseBuilder;
import lang::Syntax;
import lang::Parser;

import Message;
import ParseTree;

set[Message] testChecker() = check(spc,buildUseDefRel(spc))
  when Spec spc := parseSpec(|project://rebel2/examples/pingpong.rebel|);

set[Message] check(Spec spc, UseDef useDef) {
  set[Message] undeclaredFields = {};
  
  for (Event ev <- spc.events) {
    for (/e:(Expr)`this.<Id field>` := ev, useDef[e@\loc] == {}) {
      undeclaredFields += error("Undeclared field", e@\loc);
    }
    
    for (/e:(Expr)`<Id param>` := ev, useDef[e@\loc] == {}) {
      undeclaredFields += error("Undeclared parameter", e@\loc);
    }
  } 
  
  return undeclaredFields;
}
