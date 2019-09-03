module analysis::DefAndUseBuilder

import lang::Syntax;
import lang::Parser;

import String;
import IO;
import Set;
import List;
import ParseTree;

data Scope
  = spec(str name)
  | event(str name)
  ;

alias UseDef = rel[loc,loc, Scope];

UseDef testBuilder() = buildUseDefRel(parseSpec(|project://rebel2/examples/pingpong.rebel|));

UseDef buildUseDefRel(Spec spc) {
  result = findUses(spc);
  
  return result;
}

UseDef findUses(Spec spc) {
  UseDef result = {};
    
  map[str,Field] fields = ("<f.name>" : f | /Field f := spc);
  
  for (Event ev <- spc.events) {
    map[str,FormalParam] params = ("<p.name>" : p | FormalParam p <- ev.params);
    set[loc] specField = {};
    
    for (/e:(Expr)`this.<Id field>` := ev, "<field>" in fields) {
      result += <e@\loc, fields["<field>"]@\loc, spec("<spc.name>")>;
      specField += field@\loc;
    }
    
    for (/e:(Expr)`<Id param>` := ev) {
      if ("<param>" in params, e@\loc notin specField) {
        result += <e@\loc, params["<param>"]@\loc, event("<ev.name>")>;
      }    
    }
  }
  
  return result;
}