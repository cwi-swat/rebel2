module analysis::allealle::FormulaAndExpressionTranslator

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::RelationCollector;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import IO;
import Set;
import List;
import Map;
import ParseTree;
import util::Maybe;

data Context = ctx(Config cfg, str curRel, str stepRel);

Context nextCurRel(Context old) = ctx(old.cfg, getNextCurRel(old.curRel), old.stepRel);
Context nextStepRel(Context old) = ctx(old.cfg, old.curRel, getNextStepRel(old.stepRel));
Context nextCurAndStepRel(Context old) = ctx(old.cfg, getNextCurRel(old.curRel), getNextStepRel(old.stepRel));

str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
str translate((Formula)`!<Formula f>`, Context ctx) = "¬ (<translate(f,ctx)>)";

str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { 
  str relOfSync = translateRelExpr(spc, ctx);
  
  Spec syncedSpec = getSpecByType(spc, ctx.cfg.instances, ctx.cfg.tm);
  Event syncedEvent = lookupEventByName("<event>", syncedSpec);

  // Fix synced event param values
  list[str] actuals = ["step", "<relOfSync><maybeRename(getFieldName(spc,ctx), "instance")>"];
  
  list[FormalParam] formals = [p | FormalParam p <- syncedEvent.params];
  list[Expr] args = [a | Expr a <- params];
   
  for (int i <- [0..size(formals)]) {
    switch (args[i]) {
      case (Expr)`<Int ii>`: actuals += "__IntConst_<ii>[const_<ii>-\><formals[i].name>]"; 
      case (Expr)`<StringConstant s>`: actuals += "__StrConst_<unquote(s)>[const_<unquote(s)>-\><formals[i].name>]";
      default: actuals += "<translateRelExpr(args[i], ctx)><maybeRename(getFieldName(args[i], ctx), isPrim(formals[i].tipe,ctx.cfg.tm) ? "<formals[i].name>" : "instance")>";
    }
  }
   
  return "event<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)>[<intercalate(", ", actuals)>]";  
}  

str translate((Formula)`<Expr lhs> is <Id state>`, Context ctx) {
  str specOfLhs = getSpecTypeName(lhs, ctx.cfg.tm);
  str specRel = ctx.cfg.rm[lhs@\loc].relExpr; 
  str stateRel = "<state>" == "initialized" ?
    "initialized" :
    "State<capitalize(specOfLhs)><capitalize("<state>")>";
    
  return "inState[<ctx.curRel>, <specRel>, <stateRel>]";    
}  

str translate((Formula)`eventually <Formula f>`, Context ctx) {
  str configRel = (ctx.curRel == defaultCurRel()) ? "Config" : "(<ctx.curRel>[config as cur] ⨝ *\<cur,nxt\>order)[nxt-\>config]";
  ctx = nextCurRel(ctx);
  return "∃ <ctx.curRel> ∈ <configRel> | <translate(f, ctx)>";
} 

str translate((Formula)`always <Formula f>`, Context ctx) {
  str configRel = (ctx.curRel == defaultCurRel()) ? "Config" : "(<ctx.curRel>[config as cur] ⨝ *\<cur,nxt\>order)[nxt-\>config]";
  ctx = nextCurRel(ctx);
  return "∀ <ctx.curRel> ∈ <configRel> | <translate(f, ctx)>";
}

str translate((Formula)`next <Formula f>`, Context ctx) {
  newCtx = nextCurAndStepRel(ctx);
  return "let <newCtx.stepRel> = (order ⨝ <ctx.curRel>[config as cur]), prev = <ctx.curRel>, <newCtx.curRel> = <newCtx.stepRel>[nxt-\>config] | <translate(f, newCtx)>";
}

str translate((Formula)`first <Formula f>`, Context ctx) {
  ctx = nextCurRel(ctx);
  return "let <ctx.curRel> = first | <translate(f, ctx)>";
}

str translate((Formula)`<TransEvent event> on <Expr var> <WithAssignments? with>`, Context ctx) {
  str spec = getSpecTypeName(var, ctx.cfg.tm); 
  str r = translateRelExpr(var, ctx); 
  // TODO; handle the With assignments expression
  return "Event<capitalize(spec)><capitalize("<event>")> ⊆ (raisedEvent ⨝ <ctx.stepRel> ⨝ <r>)[event]";
}

str translate((Formula)`forall <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(∀ <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate((Formula)`exists <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(∃ <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate(current:(Decl)`<{Id ","}+ ids>: <Expr expr>`, Context ctx) {
  str te = translateRelExpr(expr, ctx);
  return intercalate(",", ["<name> ∈ <te>" | Id name <- ids]); 
} 

str translate((Formula)`<Expr lhs> in <Expr rhs>`,    Context ctx) = "some (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)>-\><getFieldName(rhs,ctx)>])";
str translate((Formula)`<Expr lhs> notin <Expr rhs>`, Context ctx) = "no (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)>-\><getFieldName(rhs,ctx)>])";

str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∧ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∨ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "(<translate(lhs,ctx)> ⇒ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "(<translate(lhs,ctx)> ⇔ <translate(rhs,ctx)>)";

str translate((Formula)`<Expr exp> = {}`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
str translate((Formula)`{} = <Expr exp>`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
default str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);
default str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\>",  ctx);

str translate((Formula)`if <Formula cond> then <Formula then> else <Formula \else>`,  Context ctx) = translate((Formula)`(<Formula cond> =\> <Formula then>) && (!(<Formula cond>) =\> <Formula \else>)`, ctx);

str translate((Formula)`noOp(<Expr expr>)`, Context ctx) {
  return "notInChangeSet[step, <ctx.cfg.rm[expr@\loc].relExpr><renameIfNecessary(expr, "instance", ctx)>]";
}

default str translate(Formula f, Context ctx) { throw "No translation function implemented yet for `<f>`"; }

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isPrim(lhs, ctx.cfg.tm) && isPrim(rhs, ctx.cfg.tm)) {
    // it is equality on attributes
    return translateRestrictionEq(lhs, rhs, op, ctx);
  } else {
    return translateRelEq(lhs, rhs, op, ctx);
  }
}

str translateRelEq(Expr lhs, Expr rhs, str op, Context ctx)  
  = "<translateRelExpr(lhs, ctx)> <op> <translateRelExpr(rhs, ctx)><maybeRename(getFieldName(rhs,ctx),getFieldName(lhs,ctx))>";

str translateRestrictionEq(Expr lhs, Expr rhs, str operator, Context ctx) {
  set[str] findReferencedRels(Expr expr) {
    set[loc] done = {};
    set[str] rels = {}; 
    
    top-down visit(expr) {
      // We only want fields and parameters
      case current:(Expr)`<Expr exp>'`: {
        RelExpr r = ctx.cfg.rm[current@\loc];
        rels += prefix(r, "nxt");
        done += exp@\loc;
      }
      case current:(Expr)`<Expr exp>.<Id fld>`: {
        RelExpr r = ctx.cfg.rm[current@\loc];
        if ((Expr)`this` := exp && current@\loc notin done) {
          rels += prefix(r, "cur");
        } else {
          role = getIdRole(exp@\loc,ctx.cfg.tm);
          if (role == paramId()) {
            rels += prefix(r, "param");
          } else if (role == quantVarId()) {
            rels += prefix(r, "<exp>");
          }
        } 
      }
      case current:(Expr)`<Id id>`: {
        if (getIdRole(current@\loc,ctx.cfg.tm) == paramId()) {
          RelExpr r = ctx.cfg.rm[current@\loc];
          rels += prefix(r, "param");
        } 
      }
    }
    
    return rels;
  }

  set[str] refRels = findReferencedRels(lhs) + findReferencedRels(rhs);
  return "(some (<intercalate(" ⨯ ", [*refRels])>) where (<translateAttrExpr(lhs,ctx)> <operator> <translateAttrExpr(rhs,ctx)>))";
}  


str translateRelExpr(current:(Expr)`(<Expr e>)`, Context ctx) = "(<translateRelExpr(e,ctx)>)";
str translateRelExpr(current:(Expr)`<Id id>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr expr>'`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr expr>.<Id field>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr spc>[<Id field>]`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;

str translateRelExpr(current:(Expr)`{<Id var> : <Expr expr> | <Formula f>}`, Context ctx) {
  str te = ctx.cfg.rm[expr@\loc].relExpr;
  return  "{<var> : <te> | <translate(f,ctx)>}"; 
}

str translateRelExpr(current:(Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr; 
str translateRelExpr(current:(Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`{<{Expr ","}* elems>}`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;

default str translateRelExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

str translateAttrExpr((Expr)`(<Expr e>)`,              Context ctx) = "(<translateAttrExpr(e,ctx)>)"; 
str translateAttrExpr((Expr)`<Id id>`,                 Context ctx) = "param_<id>";
str translateAttrExpr((Expr)`this.<Id id>`,            Context ctx) = "cur_<id>";
str translateAttrExpr((Expr)`this.<Id id>'`,           Context ctx) = "nxt_<id>";
str translateAttrExpr((Expr)`<Expr expr>.<Id fld>`,    Context ctx) = "param_<fld>" when paramId() := getIdRole(expr@\loc,ctx.cfg.tm);
str translateAttrExpr((Expr)`<Expr expr>.<Id fld>`,    Context ctx) = "<expr>_<fld>" when quantVarId() := getIdRole(expr@\loc,ctx.cfg.tm);
str translateAttrExpr((Expr)`<Lit l>`,                 Context ctx) = translateLit(l);
str translateAttrExpr((Expr)`- <Expr e>`,              Context ctx) = "- <translateAttrExpr(e,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> * <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> / <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> / <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> + <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> - <translateAttrExpr(rhs,ctx)>";

default str translateAttrExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

str translateLit((Lit)`<Int i>`) = "<i>";
str translateLit((Lit)`<StringConstant s>`) = "<s>";

str prefix(RelExpr r, str prefix) {
  if (size(r.heading) > 1) {
    throw "Can only prefix an unary relation";
  }
  
  str fld = getOneFrom(r.heading);
  return "<r.relExpr><maybeRename(fld, "<prefix>_<fld>")>";
}

str renameIfNecessary(Expr expr, str renamed, Context ctx) {
  str origName = getFieldName(expr,ctx);
  if (origName != renamed) {
    return "[<origName> as <renamed>]";
  } else {
    return "";
  }
}

str getFieldName(Expr expr, Context ctx) {
  Heading header = ctx.cfg.rm[expr@\loc].heading;
  if (size(header) > 1) {
    throw "More than 1 attribute in the relation, unable to determine field name";
  }
  
  return getOneFrom(header); 
}

str getNextCurRel(str oldCurRel) {
  if (oldCurRel == defaultCurRel()) {
    return "<defaultCurRel()>_1";
  }
  
  if (/cur_<n:[0-9]+>/ := oldCurRel) {
    return "<defaultCurRel()>_<toInt(n)+1>";
  }
}

str getNextStepRel(str oldStepRel) {
  if (oldStepRel == defaultStepRel()) {
    return "<defaultStepRel()>_1";
  }
  
  if (/step_<n:[0-9]+>/ := oldStepRel) {
    return "<defaultStepRel()>_<toInt(n)+1>";
  }
}

str defaultCurRel() = "cur";
str defaultStepRel() = "step";

private str maybeRename(str orig, str renameAs) = "[<orig> as <renameAs>]" when orig != renameAs;
private default str maybeRename(str orig, str renameAs) = "";

str getSpecTypeName(Expr expr, TModel tm) = name when specType(str name) := getType(expr, tm);
default str getSpecTypeName(Expr expr, TModel tm) { throw "Expression `<expr>` is not a Spec Type"; }

