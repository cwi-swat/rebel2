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

data Context = ctx(str cur, str nxt, str spec, str event, TModel tm);

str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
str translate((Formula)`<Expr event>(<{Expr ","}* params>)`, Context ctx) { throw "Not yet supported"; }  

str translate((Formula)`<Expr lhs> is initialized`, Context ctx) = translateMember(lhs, "initialized", ctx);
default str translate((Formula)`<Expr lhs> is <State st>`, Context ctx) { throw "Not yet supported"; }

private str translateMember(Expr lhs, str stateRel, Context ctx) { 
  str lhsRel = "";
  
  visit (ctx.useDef[lhs@\loc]<1>) {
    case event(_) : lhsRel = "(o ⨝ ParamsEvent<capitalize(ctx.spec)><capitalize(ctx.event)><capitalize("<lhs>")>)[cur-\>config,follower-\>instance]"; 
    case spec(_) : lhsRel = "TODO"; 
  }
  
  return "(<lhsRel> ⨝ instanceInState)[state] ⊆ initialized";
}

str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> && <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> || <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "(<translate(lhs,ctx)> =\> <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "(<translate(lhs,ctx)> \<=\> <translate(rhs,ctx)>)";

str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx) = translateRestrictionEquality(lhs, rhs, "=",   ctx); // when isPrimType(lhs);
//str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx) = translateRelEquality(lhs, rhs, "=",   ctx) when !isPrimType(lhs);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> != <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "!=",  ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\>",  ctx);

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
  
  return "(some (<combinedRel>) where (<translate(lhs,ctx)> <operator> <translate(rhs,ctx)>))";
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
str translate((Expr)`<Id id>`, Context ctx) = "<id>";
str translate((Expr)`this.<Id id>`, Context ctx) = "<ctx.cur><capitalize("<id>")>";
str translate((Expr)`this.<Id id>'`, Context ctx) = "<ctx.nxt><capitalize("<id>")>";
str translate((Expr)`<Expr exp>.<Id event>`, Context ctx) { throw "Not yet supported"; }
str translate((Expr)`now`, Context ctx) { throw "Not yet supported"; }
str translate((Expr)`<Lit l>`, Context ctx) = translate(l);

str translate((Expr)`- <Expr e>`, Context ctx) = "-<translate(e,ctx)>";
str translate((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translate(lhs,ctx)>  *  <translate(rhs,ctx)>";
str translate((Expr)`<Expr lhs> \\ <Expr rhs>`, Context ctx) = "<translate(lhs,ctx)> \\ <translate(rhs,ctx)>";
str translate((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translate(lhs,ctx)>  +  <translate(rhs,ctx)>";
str translate((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translate(lhs,ctx)>  -  <translate(rhs,ctx)>";

str translate((Lit)`<Int i>`) = "<i>";
str translate((Lit)`<StringConstant s>`) { throw "Not yet supported"; }
