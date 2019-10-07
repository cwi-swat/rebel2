module analysis::allealle::FormulaAndExpressionTranslator

import lang::Syntax;
import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;

import String;
import IO;
import Set;
import List;
import ParseTree;

private data Reference 
  = cur()
  | next()
  | param()
  ;
  
data Context = ctx(str cur, str nxt, str spec, str event, TModel tm, map[str var, str relation] varLookup);

str translate(Spec spc, Event event, set[Spec] allSpecs, Config cfg) {
  str renameFlattenedFields(list[Field] fields, str prefix) =
    intercalate(",", ["<f.name>-\><prefix><capitalize("<f.name>")>" | f <- fields]);

  list[str] tmpRels = [];
  map[str,str] varMapping = ();

  // first generate needed relational variables
  tmpRels += "cur<getCapitalizedSpecName(spc)>State = (o[cur-\>config] ⨝ instanceInState ⨝ inst)[state]";
  tmpRels += "nxt<getCapitalizedSpecName(spc)>State = (o[nxt-\>config] ⨝ instanceInState ⨝ inst)[state]";
  
  varMapping += ("cur_state": "cur<getCapitalizedSpecName(spc)>State", 
                 "nxt_state": "nxt<getCapitalizedSpecName(spc)>State");  
  
  list[Field] flattenFields = lookupOnePrimitiveFields(spc, cfg.tm);
  if (flattenFields != []) {
    tmpRels += "cur<getCapitalizedSpecName(spc)>Flattened = (o[cur -\> config] ⨝ <getOnePrimStateVectorName(spc)>)[<renameFlattenedFields(flattenFields, "cur")>]";
    tmpRels += "nxt<getCapitalizedSpecName(spc)>Flattened = (o[nxt -\> config] ⨝ <getOnePrimStateVectorName(spc)>)[<renameFlattenedFields(flattenFields, "nxt")>]";
  
    varMapping += ("cur_flattened": "cur<getCapitalizedSpecName(spc)>Flattened",
                   "nxt_flattened": "nxt<getCapitalizedSpecName(spc)>Flattened");
  }
  
  for (Field f <- lookupNonPrimFields(spc, cfg.tm)) {
    tmpRels += "cur<getCapitalizedSpecName(spc)><capitalize("<f.name>")> = (o[cur -\> config] ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")>)[<f.name>]";
    tmpRels += "nxt<getCapitalizedSpecName(spc)><capitalize("<f.name>")> = (o[nxt -\> config] ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")>)[<f.name>]";    
  
    varMapping += ("cur_<capitalize("<f.name>")>": "cur<getCapitalizedSpecName(spc)><capitalize("<f.name>")>",
                   "nxt_<capitalize("<f.name>")>": "nxt<getCapitalizedSpecName(spc)><capitalize("<f.name>")>");  
  }
  
  list[FormalParam] params = lookupPrimitiveParams(event, cfg.tm);
  for (params != []) {
    tmpRels += "param<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Flattened = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Primitives)[<intercalate(",", ["<p.name>" | p <- params])>]";
    varMapping += ("params_flattened": "param<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Flattened");
  }  
  
  for (FormalParam p <- lookupNonPrimParams(event, cfg.tm)) {
    tmpRels += "params<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")> = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")>)[<p.name>]";
    varMapping += ("param_<capitalize("<p.name>")>" : "params<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")>"); 
  }
  
  str lets = "let <intercalate(",\n    ", tmpRels)> |";
             
  println(lets);
  
  return "";                 
}

str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { throw "Not yet supported"; }  

str translate(f: (Formula)`<Expr lhs> is <Id state>`, Context ctx) {
  str specOfLhs = getType(lhs, ctx.tm).name;
   
  str specRel = isParam(lhs, ctx.tm) ?
    "(o ⨝ ParamsEvent<capitalize(ctx.spec)><capitalize(ctx.event)><capitalize("<lhs>")>)[cur-\>config,follower-\>instance]" : 
    "(o[cur -\> config] x (Instance |x| <capitalize(specOfLhs)>)";  
  
  str stateRel = "<state>" == "initialized" ?
    "initialized" :
    "State<capitalize(specOfLhs)><capitalize("<state>")>";
    
  return "(<specRel> |x| instanceInState)[state] in <stateRel>";    
} 

str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> && <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> || <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "(<translate(lhs,ctx)> =\> <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "(<translate(lhs,ctx)> \<=\> <translate(rhs,ctx)>)";

str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);
str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\>",  ctx);

bool referencesNextState(Expr expr) {
  visit(expr) {
    case (Expr)`<Expr _>'` : return true;
  }
  
  return false;
}

str getReferencedRel(Expr expr, Context ctx) = translate(expr, ctx);

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isAttributeType(lhs, ctx.tm) && isAttributeType(rhs, ctx.tm)) {
    // it is equality on attributes
    return translateRestrictionEquality(lhs, rhs, op, ctx);
  } else {
    return translateRelEquality(lhs, rhs, op, ctx);
  }
}

str translateRelEquality(Expr lhs, Expr rhs, str op, Context ctx) = "<translate(lhs, ctx)> <op> <translate(rhs, ctx)>"; 

str translateRestrictionEquality(Expr lhs, Expr rhs, str operator, Context ctx) {
  set[Reference] r = findReferences(lhs, ctx); 
  r += findReferences(rhs, ctx);
  
  str combinedRel = "";
  
  if (cur() in r) {
    combinedRel += ctx.cur;
  }
  if (next() in r) {
    combinedRel += (combinedRel == "") ? ctx.nxt : " x <ctx.nxt>";
  }
  if (param() in r) {
    str joined = "o |x| ParamsEvent<capitalize(ctx.spec)><capitalize(ctx.event)>Primitives";
    combinedRel += (combinedRel == "") ? joined : " x <joined>"; 
  } 
  
  return "(some (<combinedRel>) where (<translateAttr(lhs,ctx)> <operator> <translateAttr(rhs,ctx)>))";
}  

set[Reference] findReferences(Expr expr, Context ctx) {
  set[Reference] r = {};

  set[loc] nr = {};

  top-down visit(expr) {
    case (Expr)`this.<Id id>` : {if (id@\loc notin nr) r += cur();} // current state is referenced
    case (Expr)`this.<Id id>'`: {r += next(); nr += id@\loc;}// next state is referenced
    case (Expr)`<Id _>`      : r += param();  // event param is referenced
  }
  
  return r;
}
  
str translate((Expr)`(<Expr e>)`, Context ctx) = "(<translate(e,ctx,prefix)>)"; 
str translate((Expr)`<Id id>`, Context ctx) = "(o |x| ParamsEvent<capitalize(ctx.spec)><capitalize(ctx.event)><capitalize("<id>")>)[<id>]";
str translate((Expr)`this.<Id id>`, Context ctx) = "(o[cur -\> config] |x| SV<capitalize(ctx.spec)><capitalize("<id>")> |x| inst)[<id>]";
str translate((Expr)`this.<Id id>'`, Context ctx) = "(o[nxt -\> config] |x| SV<capitalize(ctx.spec)><capitalize("<id>")> |x| inst)[<id>]";

str translateAttr((Expr)`(<Expr e>)`, Context ctx) = "(<translateAttr(e,ctx,prefix)>)"; 
str translateAttr((Expr)`<Id id>`, Context ctx) = "<id>";
str translateAttr((Expr)`this.<Id id>`, Context ctx) = "<ctx.cur><capitalize("<id>")>";
str translateAttr((Expr)`this.<Id id>'`, Context ctx) = "<ctx.nxt><capitalize("<id>")>";

str translateAttr((Expr)`now`, Context ctx) { throw "Not yet supported"; }
str translateAttr((Expr)`<Lit l>`, Context ctx) = translate(l);

str translateAttr((Expr)`- <Expr e>`, Context ctx) = "-<translateAttr(e,ctx)>";
str translateAttr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  *  <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> \\ <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)> \\ <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  +  <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  -  <translateAttr(rhs,ctx)>";

str translate((Lit)`<Int i>`) = "<i>";
str translate((Lit)`<StringConstant s>`) { throw "Not yet supported"; }
