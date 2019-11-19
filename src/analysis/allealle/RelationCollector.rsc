module analysis::allealle::RelationCollector

import rebel::lang::TypeChecker;
import rebel::lang::Syntax; 

import String;

alias RelMapping = map[loc, RelExpr]; 
alias RelExpr = tuple[str relExpr, Heading heading];
alias Heading = map[str,Domain];

data Domain
  = idDom()
  | intDom()
  | strDom()
  ;

data Phase
  = curPhase()
  | nextPhase()
  ;

data AnalysisScope
  = eventScope(Phase phase=curPhase())
  | factScope()
  | assertScope()
  | actualsScope()
  ;

data AnalysisContext = actx(RelExpr (loc l) lookup, void (loc l, RelExpr r) add, AnalysisScope scp, TModel tm); 
AnalysisContext changeScope(AnalysisScope newScope, AnalysisContext old) = actx(old.lookup, old.add, newScope, old.tm);

RelMapping constructRelMapping(set[Module] mods, TModel tm) {
  RelMapping mapping = ();
  
  void addRel(loc l, RelExpr r) { mapping[l] = r; }
  RelExpr lookupRel(loc l) = mapping[l] when l in mapping;
  default RelExpr lookup(loc l) { throw "No Relation expression stored for location `l`"; }
  
  for (Module m <- mods) {
    
    // First do all the events in the specification
    for (/Spec s <- m.parts, /Event ev <- s.events) {
      analyse(ev, actx(lookupRel, addRel, eventScope(), tm));    
    }
  }
  
  return mapping; 
}

void analyse((Event)`<Modifier? modi> event <Id name>(<{FormalParam ","}* params>) <EventBody body>`, AnalysisContext ctx) {
  // Add relations for parameters
  for (FormalParam p <- params) {
    ctx.add(p.name@\loc, <"<p.name>", ("<p.name>" : type2Dom(getType(p.name@\loc, ctx.tm)))>);  
  }

  analyse(body, ctx);  
}

void analyse((EventBody)`<Pre? maybePre> <Post? maybePost> <EventVariant* variants>`, AnalysisContext ctx) {
  for (/Pre pre := maybePre, Formula f <- pre.formulas) {
    analyse(f, ctx);
  }
  
  for (/Post post := maybePost, Formula f <- post.formulas) {
    analyse(f, ctx);
  }
  
  // There should not be any variants any more since the analyzer should run on normalized specifications only
  if (/EventVariant v := variants) {
    throw "Can not analyse events with variants. Analyzer only handles normalized specifications";
  }
}

// From Common Syntax
void analyse((Formula)`(<Formula f>)`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`!<Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`<Expr spc>.<Id event>(<{Expr ","}* actuals>)`, AnalysisContext ctx) {
  analyse(spc,ctx);
  for (Expr arg <- actuals) {
    analyse(arg, changeScope(actualsScope(), ctx));
  }
}

void analyse((Formula)`<Expr spc> is <Id state>`, AnalysisContext ctx) = analyse(spc, ctx);
void analyse((Formula)`<Expr lhs> in <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> notin <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> \< <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> \<= <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> = <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> != <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> \>= <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Expr lhs> \> <Expr rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Formula lhs> && <Formula rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Formula lhs> || <Formula rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Formula lhs> =\> <Formula rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`<Formula lhs> \<=\> <Formula rhs>`, AnalysisContext ctx) { analyse(lhs, ctx); analyse(rhs,ctx); }
void analyse((Formula)`if <Formula cond> then <Formula then> else <Formula els>`, AnalysisContext ctx) { analyse(cond, ctx); analyse(\then,ctx); analyse(els,ctx);}
void analyse((Formula)`forall <{Decl ","}+ decls> | <Formula f>`, AnalysisContext ctx) {
  for (Decl d <- decls) {
    analyse(d,ctx);
  }
  analyse(f,ctx);
}

void analyse((Formula)`exists <{Decl ","}+ decls> | <Formula f>`, AnalysisContext ctx) {
  for (Decl d <- decls) {
    analyse(d,ctx);
  }
  analyse(f,ctx);
}

//From Check Syntax
void analyse((Formula)`eventually <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`always <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`next <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`first <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`<Id event> on <Expr var> <WithAssignments? \with>`, AnalysisContext ctx) = analyse(var,ctx);

// From Common Syntax
void analyse(current:(Expr)`(<Expr expr>)`, AnalysisContext ctx) {
  analyse(expr,ctx);
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}

void analyse(current:(Expr)`<Id var>`, AnalysisContext ctx) {
  Define def = getDefinition(var@\loc, ctx.tm);
  
  if (ctx.scp == eventScope()) {
    switch (def.idRole) { 
      case paramId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      case quantVarId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      default: throw "Id expression at `<current@\loc>` is used in a way not yet handled by the relation analyser";        
    }
  } else if (ctx.scope == factScope() || ctx.scope == assertScope) {
    switch (def.idRole) {
      case specId(): ctx.add(current@\loc, ("(Instance ⨝ <capitalize("var")>)[instance]" : ("instance" : idDom())));
      case quantVarId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      default: throw "Id expression at `<current@\loc>` is used in a way not yet handled by the relation analyser";        
    }
  }  
}

void analyse(current:(Expr)`<Expr expr>.<Id field>`, AnalysisContext ctx) {
  if ((Expr)`this` !:=expr && ctx.scope == eventScope()) {
    throw "Field access expression does not access field on `this`";
  }
  
  if (ctx.scope == eventScope(phase=curPhase())) {
    ;      
  }  
} 
void analyse(current:(Expr)`<Lit lit>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`<Expr expr>'`, AnalysisContext ctx) {}
void analyse(current:(Expr)`- <Expr expr>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`<Expr lhs> * <Expr rhs>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`<Expr lhs> / <Expr rhs>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`<Expr lhs> + <Expr rhs>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`<Expr lhs> - <Expr rhs>`, AnalysisContext ctx) {}
void analyse(current:(Expr)`{<Decl d> | <Formula f>}`, AnalysisContext ctx) {}
  
void analyse((Decl)`<{Id ","}+ vars>: <Expr expr>`, AnalysisContext ctx) {
  analyse(expr, ctx);
  
  for (Id var <- vars) {
    ctx.add(var@\loc, ctx.lookup(expr@\loc));
  }
}

private Define getDefinition(loc use, TModel tm) {
  if (tm.useDef has use) {
    throw "Unable to find the definition for `<use>`";
  } else if ({loc def} := tm.useDef[use]) { 
    if (def in tm.definitions) {
      return tm.definitions[def];
    } else {
      throw "Unable to define role for `<def>`";
    }
  }
}

private AType getType(loc expr, TModel tm) = tm.facts[expr] when expr in tm.facts;
private default AType getType(loc expr, TModel tm) { throw "No type information known for expression at `<expr>`"; }

private Domain type2Dom(intType()) = intDom();
private Domain type2Dom(strType()) = strDom();
private default Domain type2Dom(AType t) = idDom();