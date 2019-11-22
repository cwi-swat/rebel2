module analysis::allealle::RelationCollector

import rebel::lang::TypeChecker;
import rebel::lang::Syntax; 

import String;
import Location;
import IO;

alias RelMapping = map[loc, RelExpr]; 
alias RelExpr = tuple[str relExpr, Heading heading];
alias Heading = map[str,Domain];

data Domain
  = idDom()
  | intDom()
  | strDom()
  ;
  
data ScopeRole 
  = primedScope()
  | syncScope()
  ;  

data AnalysisContext = actx(RelExpr (loc l) lookup, void (loc l, RelExpr r) add, TModel tm, map[loc,ScopeRole] scopes); 

RelMapping constructRelMapping(set[Module] mods, TModel tm) {
  RelMapping mapping = ();
  
  void addRel(loc l, RelExpr r) { mapping[l] = r; }
  RelExpr lookupRel(loc l) = mapping[l] when l in mapping;
  default RelExpr lookup(loc l) { throw "No Relation expression stored for location `l`"; }
  
  map[loc,ScopeRole] scopes = constructScopeMap(mods, tm);
  
  for (Module m <- mods) {
    // First do all the events in the specification
    for (/Spec s <- m.parts, /Event ev <- s.events) {
      analyse(ev, actx(lookupRel, addRel, tm, scopes));    
    }
  }
  
  return mapping; 
}

private map[loc,ScopeRole] constructScopeMap(set[Module] mods, TModel tm) {
  map[loc,ScopeRole] scopes = ();
  
  visit (mods) {
    case Spec spc: scopes[spc@\loc] = eventScope();
    case Event ev: scopes[ev@\loc] = eventScope();
    case current:(Formula)`forall <{Decl ","}+ decls> | <Formula f>`: scopes[current@\loc] = quantScope();
    case current:(Formula)`exists <{Decl ","}+ decls> | <Formula f>`: scopes[current@\loc] = quantScope();
    case current:(Expr)`{<Decl d> | <Formula frm>}`: scopes[current@\loc] = quantScope();
    case current:(Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`: scopes[current@\loc] =syncScope();
    case current:(Expr)`<Expr e>'`: scopes[current@\loc] = primedScope(); 
    case Fact f: scopes[f@\loc] = factScope();
    case Assert a: scopes[a@\loc] = assertScope();
  }
  
  return scopes;
}

void analyse((Event)`<Modifier? modi> event <Id name>(<{FormalParam ","}* params>) <EventBody body>`, AnalysisContext ctx) {
  // Add relations for parameters
  for (FormalParam p <- params) {
    ctx.add(p.name@\loc, <"<p.name>", ("<p.name>" : type2Dom(getType(p.name@\loc, ctx)))>);  
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
  println("Here!");
  Define def = getDefinition(var@\loc, ctx);
  ScopeRole scp = getBaseScopeRole(def, ctx);
  
  if (scp == eventScope()) {
    switch (def.idRole) { 
      case paramId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      case quantVarId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      default: throw "Id expression at `<current@\loc>` is used in a way not yet handled by the relation analyser";        
    }
  } else if (scp == factScope() || scp == assertScope()) {
    switch (def.idRole) {
      case specId(): ctx.add(current@\loc, ("(Instance ⨝ <capitalize("var")>)[instance]" : ("instance" : idDom())));
      case quantVarId(): ctx.add(current@\loc, ctx.lookup(def.defined));
      default: throw "Id expression at `<current@\loc>` is used in a way not yet handled by the relation analyser";        
    }
  }  
}

void analyse(current:(Expr)`<Expr expr>.<Id field>`, AnalysisContext ctx) {
  Define fldDef = getDefinition(field@\loc, ctx);
  Define exprDef = getDefintion(expr@\loc, ctx);
  
  ScopeRole scp = getBaseScopeRole(fldDef, ctx);
  
  if (scp == eventScope()) {
    if ((Expr)`this.<Id field>` := current) {
      Heading h = ("<field>" : type2Dom(getType(field@\loc, ctx)));
      str relName = (primedScope() := getContainingScopeRole(current@\loc, ctx)) ? "nxt<capitalize("<field>")>" : "cur<capitalize("<field>")>";
      
      ctx.add(current@\loc, <relName, h>);
    } else if (exprDef.idRole == specId(), specType(str name) := getType(expr@\loc, ctx)) {
      ;
    } 
  }
} 
void analyse(current:(Expr)`<Lit lit>`, AnalysisContext ctx) {}

void analyse(current:(Expr)`<Expr expr>'`, AnalysisContext ctx) {
  analyse(expr, ctx);
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}

void analyse(current:(Expr)`- <Expr expr>`, AnalysisContext ctx) {
  analyse(expr, ctx);
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}
void analyse(current:(Expr)`<Expr lhs> * <Expr rhs>`, AnalysisContext ctx) {analyse(lhs,ctx); analyse(rhs,ctx);}
void analyse(current:(Expr)`<Expr lhs> / <Expr rhs>`, AnalysisContext ctx) {analyse(lhs,ctx); analyse(rhs,ctx);}
void analyse(current:(Expr)`<Expr lhs> + <Expr rhs>`, AnalysisContext ctx) {analyse(lhs,ctx); analyse(rhs,ctx);}
void analyse(current:(Expr)`<Expr lhs> - <Expr rhs>`, AnalysisContext ctx) {analyse(lhs,ctx); analyse(rhs,ctx);}
void analyse(current:(Expr)`{<Decl d> | <Formula f>}`, AnalysisContext ctx) {analyse(d,ctx); analyse(f,ctx);}
  
void analyse((Decl)`<{Id ","}+ vars>: <Expr expr>`, AnalysisContext ctx) {
  analyse(expr, ctx);
  
  for (Id var <- vars) {
    ctx.add(var@\loc, ctx.lookup(expr@\loc));
  }
}

private Define getDefinition(loc use, AnalysisContext ctx) {
  if (ctx.tm.useDef has use) {
    throw "Unable to find the definition for `<use>`";
  } else if ({loc def} := ctx.tm.useDef[use]) { 
    if (def in ctx.tm.definitions) {
      return ctx.tm.definitions[def];
    } else {
      throw "Unable to define role for `<def>`";
    }
  }
}

@memo
private rel[loc,loc] getContainmentRel(set[loc] scopes) {
  rel[loc,loc] containment = {};
  
  for (l <- scopes, other <- scopes, l != other, isContainedIn(l,other)) {
    containment += <l,other>;
  }
  
  return containment;
}

private ScopeRole getBaseScopeRole(Define d, AnalysisContext ctx) {
  ScopeRole currentRole = getScopeRole(d, ctx);
  
  rel[loc,loc] containment = getContainmentRel(ctx.scopes<0>);
  loc largest = d.scope;
  while (/<largest, loc other> := containment) {
    largest = other;
  }     
  
  return ctx.scopes[largest];
}

private ScopeRole getContainingScopeRole(loc l, AnalysisContext ctx) {
  bool found = false;
  set[loc] scopes = ctx.scopes<0>;
    
  loc smallest = l.top;
  for (loc other <- scopes, isContainedIn(l, other), isContainedIn(other, smallest)) {
    smallest = other;
    found = true;
  }
  
  if (!found) {
    throw "Unable to find containing scope for location `<l>`";
  }
  
  return ctx.scopes[smallest];  
}

private ScopeRole getScopeRole(Define d, AnalysisContext ctx) = ctx.scopes[d.scope] when d.scope in ctx.scopes;
private default ScopeRole getScopeRole(Define d, AnalysisContext ctx) { throw "Unable to find scope for scope definition at `<d.scope>`"; }  

private AType getType(loc expr, AnalysisContext ctx) = ctx.tm.facts[expr] when expr in ctx.tm.facts;
private default AType getType(loc expr, AnalysisContext ctx) { throw "No type information known for expression at `<expr>`"; }

private Domain type2Dom(intType()) = intDom();
private Domain type2Dom(strType()) = strDom();
private default Domain type2Dom(AType t) = idDom();

str dom2Str(intType()) = "int";
str dom2Str(strType()) = "str";
default str dom2Str(AType t) = "id";