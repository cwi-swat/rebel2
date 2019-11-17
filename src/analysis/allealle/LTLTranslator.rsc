module analysis::allealle::LTLTranslator

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::EventTranslator;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import IO;
import Set;
import Map;
import List;

alias RelHeader = map[str attName, str attDomain];
data Context = ctx(RelHeader (loc) lookupHeader, void (loc, RelHeader) addHeader, str curConfigRel, TModel tm);

Context newCtx(str curConfigRel, Context oldCtx) = ctx(oldCtx.lookupHeader, oldCtx.addHeader, curConfigRel, oldCtx.tm); 

str buildAssert(str assertName, set[Module] mods, TModel tm) {
  map[loc,RelHeader] rl = ();
  RelHeader lookupHeader(loc expr) = rl[expr] when expr in rl; 
  default RelHeader lookupHeader(loc expr) { throw "Expression location not in rel header map"; }
  void addHeader(loc expr, RelHeader header) { rl += (expr:header); }
    
  if (Module m <- mods, /(Assert)`assert <Id name> = <Formula form>;` <- m.parts, "<name>" == assertName) {
    return translate(form, ctx(lookupHeader, addHeader, "", tm)); 
  }
}

str translateFacts(set[Fact] facts, TModel tm) {
  map[loc,RelHeader] rl = ();
  RelHeader lookupHeader(loc expr) = rl[expr] when expr in rl; 
  default RelHeader lookupHeader(loc expr) { throw "Expression location not in rel header map"; }
  void addHeader(loc expr, RelHeader header) { rl += (expr:header); }
  
  list[str] alleFacts = ["// Fact: <f.name>
                        '<translate(f.form, ctx(lookupHeader, addHeader, "", tm))>" | Fact f <- facts];  

  return intercalate("\n", alleFacts);
}

str getFieldName(Expr expr, Context ctx) {
  RelHeader header = ctx.lookupHeader(expr@\loc);
  if (size(header) > 1) {
    throw "More than 1 attribute in the relation, unable to determine field name";
  }
  
  return getOneFrom(header); 
}

str getSpecTypeName(Expr expr, TModel tm) = name when specType(str name) := getType(expr, tm);
default str getSpecTypeName(Expr expr, TModel tm) { throw "Expression `<expr>` is not a Spec Type"; }

str translate((Formula)`eventually <Formula f>`, Context ctx) {
  str configRel = (ctx.curConfigRel == "") ? "Config" : "(<ctx.curConfigRel>[config as cur] ⨝ *\<cur,nxt\>order)[nxt-\>config]";
  ctx = newCtx("cur", ctx);
  return "∃ cur ∈ <configRel> | <translate(f, ctx)>";
} 

str translate((Formula)`always <Formula f>`, Context ctx) {
  str configRel = (ctx.curConfigRel == "") ? "Config" : "(<ctx.curConfigRel>[config as cur] ⨝ *\<cur,nxt\>order)[nxt-\>config]";
  ctx = newCtx("cur", ctx);
  return "∀ cur ∈ <configRel> | <translate(f, ctx)>";
}

str translate((Formula)`forall <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(∀ <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate((Formula)`exists <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(∃ <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate((Decl)`<{Id ","}+ ids>: <Expr expr>`, Context ctx) 
  = intercalate(",", ["<name> ∈ <te>" | Id name <- ids])
  when str te := translateRelExpr(expr, ctx); 


str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
str translate((Formula)`!<Formula f>`, Context ctx) = "¬ (<translate(f,ctx)>)";

str translate((Formula)`<Expr lhs> is <Id state>`, Context ctx) {
  str specOfLhs = getSpecTypeName(lhs, ctx.tm);
  
  translateRelExpr(lhs, ctx);
  str relation = getFieldName(lhs,ctx);

  str stateRel = "<state>" == "initialized" ?
    "initialized" :
    "State<capitalize(specOfLhs)><capitalize("<state>")>";
    
  return "inState[cur, <relation>, <stateRel>]";    
} 

str translate((Formula)`<Expr lhs> in <Expr rhs>`,    Context ctx) = "some (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)> -\> <getFieldName(rhs,ctx)>])";
str translate((Formula)`<Expr lhs> notin <Expr rhs>`, Context ctx) = "no (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)> -\> <getFieldName(rhs,ctx)>])";

str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "<translate(lhs,ctx)> ∧ <translate(rhs,ctx)>";
str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "<translate(lhs,ctx)> ∨ <translate(rhs,ctx)>";
str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "<translate(lhs,ctx)> ⇒ <translate(rhs,ctx)>";
str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "<translate(lhs,ctx)> ⇔ <translate(rhs,ctx)>";

str translate((Formula)`<Expr exp> = {}`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
str translate((Formula)`{} = <Expr exp>`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
default str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);
default str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\>",  ctx);

str translate((Formula)`if <Formula cond> then <Formula then> else <Formula \else>`,  Context ctx) 
  = translate((Formula)`(<Formula cond> =\> <Formula then>) ∧ (!(<Formula cond>) =\> <Formula \else>)`, ctx);

default str translate(Formula f, Context ctx) { throw "No translation function implemented yet for `<f>`"; }

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isAttributeType(lhs, ctx.tm) && isAttributeType(rhs, ctx.tm)) {
    // it is equality on attributes
    return translateRestrictionEq(lhs, rhs, op, ctx);
  } else {
    return translateRelEq(lhs, rhs, op, ctx);
  }
}

str translateRelEq(Expr lhs, Expr rhs, str op, Context ctx) 
  = "<translateRelExpr(lhs, ctx)> <op> <translateRelExpr(rhs, ctx)>"; 

set[str] gatherRels(Expr expr, Context ctx) {
  set[loc] done = {};
  set[str] rels = {};
  
  top-down visit(expr) {
    case cur:(Expr)`<Expr spc>.<Id field>`: {
      rels += translateRelExpr(cur, ctx);
      done += spc@\loc;
    }
    case cur:(Expr)`<Id id>`: {
      if (cur@\loc notin done) {
        rels += translateRelExpr(cur, ctx);
      }
    }
  }
  
  return rels;
}

str translateRestrictionEq(Expr lhs, Expr rhs, str operator, Context ctx) {
  set[str] rels = gatherRels(lhs,ctx) + gatherRels(rhs,ctx);
    
  return "(some (<intercalate(" ⨯ ", toList(rels))>) where (<translateAttrExpr(lhs,ctx)> <operator> <translateAttrExpr(rhs,ctx)>))";
}  

str translateRelExpr(current:(Expr)`(<Expr e>)`, Context ctx) {
  str res = translateRelExpr(e,ctx);
  ctx.addHeader(current@\loc, ctx.lookupHeader(e@\loc));
  
  return  "(<res>)"; 
}

str translateRelExpr(current:(Expr)`<Expr spcExpr>.<Id field>`, Context ctx) {
  str spc = "";
  if (specType(str name) := getType(spcExpr, ctx.tm)) {
    spc = name;
  } else {
    throw "Left hand side is not a spec?";
  }
  
  str renameIfPrim() = "[<field>-\><spcExpr><capitalize("<field>")>]" when isPrim(getType(field,ctx.tm));
  default str renameIfPrim() = "[<field>]";
  
  str resultRel = "(<translateRelExpr(spcExpr, ctx)> ⨝ <spc><capitalize("<field>")><if (ctx.curConfigRel != "") {> ⨝ <ctx.curConfigRel><}>)<renameIfPrim()>";

  ctx.addHeader(current@\loc, ("<field>": type2Str(getType(field, ctx.tm))));
  return resultRel;  
}

str translateRelExpr(current:(Expr)`<Id id>`, Context ctx) {
  ctx.addHeader(current@\loc, ("<id>": type2Str(getType(current,ctx.tm))));
  
  switch (getType(current, ctx.tm)) {
    case specType(str specName): {
      if ("<id>" == specName) { // its a reference to the specification it self 
        return "(<specName> ⨝ Instance)[instance]"; 
      } else {
        return "<id>";
      }
    }
  }
}

str translateRelExpr(current:(Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = translateSetRelExpr(current@\loc, lhs, rhs, "+", ctx); 
str translateRelExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = translateSetRelExpr(current@\loc, lhs, rhs, "-", ctx);
default str translateRelExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

private str translateSetRelExpr(loc current, Expr lhs, Expr rhs, str op, Context ctx) {
  str lhsRes = translateRelExpr(lhs,ctx);
  str rhsRes = translateRelExpr(rhs,ctx);
  
  str lhsFieldName = getFieldName(lhs, ctx);
  str rhsFieldName = getFieldName(rhs, ctx);
  ctx.addHeader(current, (lhsFieldName : type2Str(getType(lhs, ctx.tm))));
  
  return "(<lhsRes> <op> <rhsRes>)";
}

str translateAttrExpr((Expr)`(<Expr e>)`, Context ctx) = "(<translateAttrExpr(e,ctx,prefix)>)"; 
str translateAttrExpr((Expr)`<Id id>`, Context ctx) = "<id>";
str translateAttrExpr((Expr)`<Expr spc>.<Id id>`, Context ctx) = "<spc><capitalize("<id>")>";

str translateAttrExpr((Expr)`now`, Context ctx) { throw "Not yet supported"; }
str translateAttrExpr((Expr)`<Lit l>`, Context ctx) = translateLit(l);

str translateAttrExpr((Expr)`- <Expr e>`, Context ctx) = "-<translateAttrExpr(e,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> * <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> / <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> \\ <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> + <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> - <translateAttrExpr(rhs,ctx)>";

default str translateAttrExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

str translateLit((Lit)`<Int i>`) = "<i>";
str translateLit((Lit)`<StringConstant s>`) = "<s>";

