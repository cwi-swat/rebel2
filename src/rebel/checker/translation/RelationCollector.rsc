module rebel::checker::translation::RelationCollector

import rebel::lang::TypeChecker;
import rebel::lang::Syntax; 

import String;
import Location;
import IO;
import Map;
import util::Maybe;

alias RelMapping = map[loc, RelExpr]; 
alias RelExpr = tuple[str relExpr, Heading heading];
alias Heading = map[str,Domain];

data Domain
  = idDom()
  | intDom()
  | strDom()
  ;
  
data AnalysisContext = actx(RelExpr (loc l) lookup, void (loc l, RelExpr r) add, str curRel, str stepRel, TModel tm, map[loc,Spec] specs, set[str] emptySpecs, void (loc,str) addCurRelScoped, str (loc) lookupCurRelScoped); 

AnalysisContext nextCurRel(AnalysisContext old) = actx(old.lookup, old.add, getNextCurRel(old.curRel), old.stepRel, old.tm, old.specs, old.emptySpecs, old.addCurRelScoped, old.lookupCurRelScoped);
AnalysisContext newCurRel(str newCurRel, AnalysisContext old) = actx(old.lookup, old.add, newCurRel, old.stepRel, old.tm, old.specs, old.emptySpecs, old.addCurRelScoped, old.lookupCurRelScoped);

AnalysisContext nextStepRel(AnalysisContext old) = actx(old.lookup, old.add, old.curRel, getNextStepRel(old.stepRel), old.tm, old.specs, old.emptySpecs, old.addCurRelScoped, old.lookupCurRelScoped);

AnalysisContext nextCurAndStepRel(AnalysisContext old) = actx(old.lookup, old.add, getNextCurRel(old.curRel), getNextStepRel(old.stepRel), old.tm, old.specs, old.emptySpecs, old.addCurRelScoped, old.lookupCurRelScoped);

RelMapping constructRelMapping(Module m, TModel tm) {
  RelMapping mapping = ();
  void addRel(loc l, RelExpr r) { mapping[l] = r; }
  RelExpr lookupRel(loc l) = mapping[l] when l in mapping;
  default RelExpr lookupRel(loc l) { throw "No Relation expression stored for location `<l>`"; }
  
  map[loc,str] curRelScoped = ();
  void addCurRelScoped(loc l, str r) { curRelScoped[l] = r; }
  str lookupCurRelScoped(loc l) = curRelScoped[l] when l in curRelScoped;
  default str lookupCurRelScoped(loc l) { throw "No current relation stored for expression at <l>"; }
  
  map[loc,Spec] specs = (s@\loc : s | /Spec s <- m.parts); 
  set[str] emptySpecs = findEmptySpecs(m);
  
  AnalysisContext ctx = actx(lookupRel, addRel, defaultCurRel(), defaultStepRel(), tm, specs, emptySpecs, addCurRelScoped, lookupCurRelScoped);
  
  // First do all the events in the specification
  for (/Spec s <- m.parts) {
    for (Event ev <- s.events) {
      analyse(ev, "<s.name>", ctx);
    }
    
    for (Fact f <- s.facts) {
      analyse(f,ctx);
    }        
  }
    
  for (/Assert a <- m.parts) {
    analyse(a,ctx);
  }
  
  return mapping; 
}

private set[str] findEmptySpecs(Module m) = {"<s.name>" | /Spec s <- m.parts, isEmptySpec(s)};
private bool isEmptySpec(Spec spc) = /Transition _ !:= spc.states;

void analyse(current:(Event)`<Modifier* _> event <Id name>(<{FormalParam ","}* params>) <EventBody body>`, str specName, AnalysisContext ctx) {
  // Add relations for parameters
  for (FormalParam p <- params) {
    str fldName = isPrim(p.name@\loc,ctx) ? "<p.name>" : "instance"; 
    ctx.add(p.name@\loc, <"<p.name>", (fldName : type2Dom(getType(p.name@\loc, ctx)))>);
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

void analyse(Fact f, AnalysisContext ctx) = analyse(f.form, ctx);
void analyse(Assert a, AnalysisContext ctx) = analyse(a.form, ctx);

// From Common Syntax
void analyse((Formula)`(<Formula f>)`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`!<Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`<Expr spc>.<Id event>(<{Expr ","}* actuals>)`, AnalysisContext ctx) {
  analyse(spc,ctx);
  for (Expr arg <- actuals) {
    analyse(arg, ctx);
  }
}

void analyse((Formula)`<Expr spc> is <QualifiedName state>`, AnalysisContext ctx) = analyse(spc, ctx);
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
void analyse((Formula)`if <Formula cond> then <Formula then>`, AnalysisContext ctx) { analyse(cond, ctx); analyse(\then,ctx);}
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

void analyse((Formula)`noOp(<Expr expr>)`, AnalysisContext ctx) { analyse(expr,ctx); }

void analyse((Formula)`eventually <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`always <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`always-last <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`next <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`first <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);
void analyse((Formula)`last <Formula f>`, AnalysisContext ctx) = analyse(f,ctx);

void analyse((Formula)`<Formula u> until <Formula r>`, AnalysisContext ctx) {
 analyse(u,ctx);
 analyse(r,ctx);
}

void analyse((Formula)`<TransEvent event> on <Expr var> <WithAssignments? w>`, AnalysisContext ctx) { 
  analyse(var,ctx);
  
  for (/(Assignment)`<Id fieldName> = <Expr val>` <- w) {
    analyse(val,ctx);
  }
}

void analyse((WithAssignments)`with <{Assignment ","}+ assignments>`, AnalysisContext ctx) {}

// From Common Syntax
void analyse(current:(Expr)`(<Expr expr>)`, AnalysisContext ctx) {
  analyse(expr,ctx);
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
} 
 
void analyse(current:(Expr)`<Id var>`, AnalysisContext ctx)  {
  analyse(var,ctx);
  ctx.add(current@\loc, ctx.lookup(var@\loc));
}

void analyse(current:(Expr)`<Lit l>`, AnalysisContext ctx) {
  analyse(l,ctx);
  ctx.add(current@\loc, ctx.lookup(l@\loc));
}

void analyse(current:(Id)`<Id var>`, AnalysisContext ctx) {
  Define def = getDefinition(var@\loc, ctx);

  switch (def.idRole) { 
    case paramId(): ctx.add(current@\loc, ctx.lookup(def.defined));
    case quantVarId(): ctx.add(current@\loc, <"<var>", ctx.lookup(def.defined).heading>);
    case fieldId(): ctx.add(current@\loc, <"(<getSpecName(current@\loc,ctx)><capitalize("<var>")> ⨝ <ctx.curRel>)", ("instance":idDom(), "<var>": type2Dom(getType(current@\loc,ctx)))>);
    case specId(): ctx.add(current@\loc, <"(Instance ⨝ <capitalize("<var>")>)[instance]", ("instance":idDom())>);
    case specInstanceId(): ctx.add(current@\loc, <"<getSpecName(current@\loc,ctx)>_<var>", ("instance":idDom())>);
    default: throw "Id expression at `<current@\loc>` with role `<def.idRole>` is used in a way not yet handled by the relation analyser";        
  }
}

void analyse(current:(Expr)`<Expr expr>.<Id fld>`, AnalysisContext ctx) {
  analyse(expr,ctx);
  RelExpr exprRel  = ctx.lookup(expr@\loc);

  if (getType(expr@\loc, ctx) == stringType() && "<fld>" == "length") {
    // built-in attribute on string
    ctx.add(current@\loc, <"(<exprRel.relExpr>)[<getFieldName(exprRel)>]", ("<getFieldName(exprRel)>":type2Dom(intType()))>);  
  } else {
    analyse(fld,ctx);
    RelExpr fieldRel = ctx.lookup(fld@\loc);
    
    ctx.add(current@\loc, <"(<exprRel.relExpr><renameIfNeeded(getFieldName(exprRel),"instance")> ⨝ <fieldRel.relExpr>)[<fld>]", ("<fld>":type2Dom(getType(fld@\loc,ctx)))>);
  }
}

void analyse(current:(Expr)`<Expr expr>.*<Id fld>`, AnalysisContext ctx) {
  analyse(expr,ctx);
  analyse(fld,ctx);

  RelExpr exprRel  = ctx.lookup(expr@\loc); 
  RelExpr fieldRel = ctx.lookup(fld@\loc);

  ctx.add(current@\loc, <"(<exprRel.relExpr><renameIfNeeded(getFieldName(exprRel),"instance")> ⨝ *(<fieldRel.relExpr>)[instance,<fld>])[<fld>]", ("<fld>": type2Dom(getType(fld@\loc,ctx)))>); 
}  

void analyse(current:(Expr)`<Expr expr>.^<Id fld>`, AnalysisContext ctx) {
  analyse(expr,ctx);
  analyse(fld,ctx);

  RelExpr exprRel  = ctx.lookup(expr@\loc); 
  RelExpr fieldRel = ctx.lookup(fld@\loc);

  ctx.add(current@\loc, <"(<exprRel.relExpr><renameIfNeeded(getFieldName(exprRel),"instance")> ⨝ ^(<fieldRel.relExpr>)[instance,<fld>])[<fld>]", ("<fld>": type2Dom(getType(fld@\loc,ctx)))>); 
}  

void analyse(current:(Expr)`<Id func>(<{Expr ","}* actuals>)`, AnalysisContext ctx) {
  list[Expr] params = [p | p <- actuals];
  for (p <- params) {
    analyse(p,ctx);
  }
  
  switch ("<func>") {
    case "substr": {
      RelExpr strFld = ctx.lookup(params[0]@\loc);
      ctx.add(current@\loc, <"<strFld.relExpr>[<getFieldName(strFld)>]", ("<getFieldName(strFld)>":type2Dom(stringType()))>);
    }
    case "toInt": {
      RelExpr strFld = ctx.lookup(params[0]@\loc);
      ctx.add(current@\loc, <"<strFld.relExpr>[<getFieldName(strFld)>]", ("<getFieldName(strFld)>":type2Dom(intType()))>);    
    }
    case "toStr": {
      RelExpr intFld = ctx.lookup(params[0]@\loc);
      ctx.add(current@\loc, <"<intFld.relExpr>[<getFieldName(intFld)>]", ("<getFieldName(intFld)>":type2Dom(stringType()))>);    
    }
  }
}

void analyse(current:(Expr)`<Expr spc>[<Id fld>]`, AnalysisContext ctx) {
  analyse(spc,ctx);
  analyse(fld,ctx);
  
  RelExpr exprRel  = ctx.lookup(spc@\loc);
  RelExpr fieldRel = ctx.lookup(fld@\loc);
  
  ctx.add(current@\loc, <"<fieldRel.relExpr>", ("instance":type2Dom(getType(fld@\loc,ctx)))>);
}

void analyse(current:(Expr)`<Expr expr>'`, AnalysisContext ctx) {
  analyse(expr, newCurRel("nxt", ctx));
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}

void analyse(current:(Expr)`- <Expr expr>`, AnalysisContext ctx) {
  analyse(expr, ctx);
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}

void analyse(current:(Expr)`|<Expr expr>|`, AnalysisContext ctx) {
  analyse(expr, ctx);
  AType tipe = getType(expr@\loc,ctx);
  if (intType() := tipe) {
    ctx.add(current@\loc, ctx.lookup(expr@\loc));
  } else if (setType(_) := tipe || spectType(_) := tipe) {
    RelExpr re = ctx.lookup(expr@\loc);
    ctx.add(current@\loc, re);
  }
}

private void setOperation(loc current, Expr lhs, Expr rhs, str op, AnalysisContext ctx) {
  RelExpr lhsRel = ctx.lookup(lhs@\loc);
  RelExpr rhsRel = ctx.lookup(rhs@\loc);
  
  str relExpr = "(<lhsRel.relExpr> <op> <rhsRel.relExpr><renameIfNeeded(rhsRel, lhsRel)>)";
  ctx.add(current, <relExpr, lhsRel.heading>);
}

void analyse(current:(Expr)`<Expr lhs> + <Expr rhs>`, AnalysisContext ctx) {
  analyse(lhs,ctx); 
  analyse(rhs,ctx);

  switch ({getType(lhs@\loc, ctx), getType(rhs@\loc, ctx)}) {
    case {setType(AType tipe), tipe}: setOperation(current@\loc, lhs, rhs, "∪", ctx);
    case {setType(AType tipe), setType(tipe)}: setOperation(current@\loc, lhs, rhs, "∪", ctx);
    case {intType()}: ctx.add(current@\loc, ctx.lookup(lhs@\loc));  
  }  
}

void analyse(current:(Expr)`<Expr lhs> - <Expr rhs>`, AnalysisContext ctx) {
  analyse(lhs,ctx); 
  analyse(rhs,ctx);

  switch ({getType(lhs@\loc,ctx), getType(rhs@\loc,ctx)}) {
    case {setType(AType tipe), tipe}: setOperation(current@\loc, lhs, rhs, "∖", ctx);
    case {setType(AType tipe), setType(tipe)}: setOperation(current@\loc, lhs, rhs, "∖", ctx);
    case {intType()}: ctx.add(current@\loc, ctx.lookup(lhs@\loc));  
  }  
}

void analyse(current:(Expr)`<Expr lhs> * <Expr rhs>`, AnalysisContext ctx) = analyseBinOp(lhs,rhs,current@\loc,ctx);
void analyse(current:(Expr)`<Expr lhs> / <Expr rhs>`, AnalysisContext ctx) = analyseBinOp(lhs,rhs,current@\loc,ctx);
void analyse(current:(Expr)`<Expr lhs> % <Expr rhs>`, AnalysisContext ctx) = analyseBinOp(lhs,rhs,current@\loc,ctx);

void analyseBinOp(Expr lhs, Expr rhs, loc complete, AnalysisContext ctx) {  
  analyse(lhs,ctx); 
  analyse(rhs,ctx);
  
  ctx.add(complete, ctx.lookup(lhs@\loc));  
}

void analyse(current:(Expr)`<Expr lhs> ++ <Expr rhs>`, AnalysisContext ctx) {
  analyse(lhs,ctx); 
  analyse(rhs,ctx);

  switch ({getType(lhs@\loc, ctx), getType(rhs@\loc, ctx)}) {
    case {strType()}: ctx.add(current@\loc, ctx.lookup(lhs@\loc));  
  }  
}


void analyse(current:(Expr)`{<Decl d> | <Formula f>}`, AnalysisContext ctx) {
  analyse(d,ctx); 
  analyse(f,ctx);
  
  ctx.add(current@\loc, ctx.lookup(d@\loc));
}
  
void analyse(current:(Decl)`<{Id ","}+ vars>: <Expr expr>`, AnalysisContext ctx) {
  analyse(expr, ctx);
  
  for (Id var <- vars) {
    ctx.add(var@\loc, ctx.lookup(expr@\loc));
    ctx.addCurRelScoped(var@\loc, ctx.curRel);
  }
  
  ctx.add(current@\loc, ctx.lookup(expr@\loc));
}

void analyse(current:(Lit)`this`, AnalysisContext ctx) {
  ctx.add(current@\loc, <"<toLowerCase(getSpecName(current@\loc,ctx))>", ("instance": idDom())>);
}

void analyse(current:(Lit)`<Int i>`, AnalysisContext ctx) {
  ctx.add(current@\loc, <"__IntConst_<i>", ("const_<i>":intDom())>); 
}

void analyse(current:(Lit)`none`, AnalysisContext ctx) {
  ctx.add(current@\loc, <"__EMPTY", ("instance":idDom())>); 
}

void analyse(current:(Lit)`<StringConstant s>`, AnalysisContext ctx) {
  ctx.add(current@\loc, <"__StrConst_<unquote(s)>", ("const_<unquote(s)>":strDom())>);
}

void analyse(current:(Lit)`{<{Expr ","}* elems>}`, AnalysisContext ctx) {
  if ((Lit)`{}` := current) {
    ctx.add(current@\loc, <"__EMPTY", ("instance":idDom())>);
  }
} 

private str unquote(StringConstant s) = "<s>"[1..-1];

private str getSpecName(loc l, AnalysisContext ctx) { 
  Define d = getDefinition(l, ctx);

  if (d.defined in ctx.specs) {
    return "<ctx.specs[d.defined].name>";
  } else if (d.scope in ctx.specs) {
    return "<ctx.specs[d.scope].name>";
  } else {
    println("Something is wrong: <d>");
    throw "Unable to determine spec for `<d.id>` at <l>"; 
  }
}

private Define getDefinition(loc use, AnalysisContext ctx) {
  //if (use notin ctx.tm.useDef<0>) {
  //  throw "Unable to find the definition for `<use>`";
  //} 
  
  if ({loc def} := ctx.tm.useDef[use]) { 
    if (def in ctx.tm.definitions) {
      return ctx.tm.definitions[def];
    } 
  }
  
  throw "Unable to define role";
}

private Maybe[Define] getDefinitionIfExists(loc use, AnalysisContext ctx) {
  if (use notin ctx.tm.useDef<0>) {
    return nothing();
  } 
  
  if ({loc def} := ctx.tm.useDef[use]) { 
    if (def in ctx.tm.definitions) {
      return just(ctx.tm.definitions[def]);
    } 
  }
  
  return nothing();
}


private str getFieldName(RelExpr re) {
  if (size(re.heading) > 1) {
    throw "More than 1 attribute in the relation, unable to determine field name";
  }
  
  return getOneFrom(re.heading); 
}

private str renameIfNeeded(RelExpr lhs, RelExpr rhs) {
  if (lhs.heading == rhs.heading) {
    return "";
  }
  
  return "[<getFieldName(lhs)> as <getFieldName(rhs)>]"; 
}

private str renameIfNeeded(str lhs, str rhs) {
  if (lhs == rhs) {
    return "";
  }
  
  return "[<lhs> as <rhs>]"; 
}

private bool isPrim(loc expr, AnalysisContext ctx) = isPrim(t) when AType t := getType(expr, ctx);

private bool isPrim(intType()) = true;
private bool isPrim(stringType()) = true;
private default bool isPrim(AType t) = false;

private AType getType(loc expr, AnalysisContext ctx) = ctx.tm.facts[expr] when expr in ctx.tm.facts;
private default AType getType(loc expr, AnalysisContext ctx) { throw "No type information known for expression at `<expr>`"; }

private Domain type2Dom(intType()) = intDom();
private Domain type2Dom(stringType()) = strDom();
private default Domain type2Dom(AType t) = idDom();

str dom2Str(intType()) = "int";
str dom2Str(stringType()) = "str";
default str dom2Str(AType t) = "id";

private str getNextCurRel(str oldCurRel) {
  if (oldCurRel == defaultCurRel()) {
    return "<defaultCurRel()>_1";
  } else if (/cur_<n:[0-9]+>/ := oldCurRel) {
    return "<defaultCurRel()>_<toInt(n)+1>";
  }
  
  throw "Should not happen";
}

private str getNextStepRel(str oldStepRel) {
  if (oldStepRel == defaultStepRel()) {
    return "<defaultStepRel()>_1";
  } else if (/step_<n:[0-9]+>/ := oldStepRel) {
    return "<defaultStepRel()>_<toInt(n)+1>";
  }
  
  throw "Should not happen";
}

private str defaultCurRel() = "cur";
private str defaultStepRel() = "step";
