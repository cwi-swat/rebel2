module rebel::checker::translation::FormulaAndExpressionTranslator

import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::translation::RelationCollector;
import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import IO;
import Set;
import List;
import Map;
import ParseTree;
import util::Maybe;

data Context = ctx(RelMapping rm, TModel tm, set[Spec] allSpecs, bool topLevelLtl, str curRel, str stepRel, int () nxtUniquePrefix);

Context nextCurRel(Context old) = ctx(old.rm, old.tm, old.allSpecs, old.topLevelLtl, getNextCurRel(old.curRel), old.stepRel, old.nxtUniquePrefix);
Context nextStepRel(Context old) = ctx(old.rm, old.tm, old.allSpecs, old.topLevelLtl, old.curRel, getNextStepRel(old.stepRel), old.nxtUniquePrefix);
Context nextCurAndStepRel(Context old) = ctx(old.rm, old.tm, old.allSpecs, old.topLevelLtl, getNextCurRel(old.curRel), getNextStepRel(old.stepRel), old.nxtUniquePrefix);

Context flipTopLevelLtl(Context old) = ctx(old.rm, old.tm, old.allSpecs, false, old.curRel, old.stepRel, old.nxtUniquePrefix);

str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
str translate((Formula)`!<Formula f>`, Context ctx) = "¬ (<translate(f,ctx)>)";

str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { 
  str relOfSync = translateRelExpr(spc, ctx);
  
  Spec syncedSpec = getSpecByType(spc, ctx.allSpecs, ctx.tm);
  Event syncedEvent = lookupEventByName("<event>", syncedSpec);

  // Fix synced event param values
  list[str] actuals = [ctx.stepRel, "<relOfSync><maybeRename(getFieldName(spc,ctx), "instance")>"];
  
  list[FormalParam] formals = [p | FormalParam p <- syncedEvent.params];
  list[Expr] args = [a | Expr a <- params];
   
  for (int i <- [0..size(formals)]) {
    switch (args[i]) {
      case (Expr)`<Int ii>`: actuals += "__IntConst_<ii>[const_<ii>-\><formals[i].name>]"; 
      case (Expr)`<StringConstant s>`: actuals += "__StrConst_<unquote(s)>[const_<unquote(s)>-\><formals[i].name>]";
      default: actuals += "<translateRelExpr(args[i], ctx)><maybeRename(getFieldName(args[i], ctx), isPrim(formals[i].tipe,ctx.tm) ? "<formals[i].name>" : "instance")>";
    }
  }
   
  return "event<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)>[<intercalate(", ", actuals)>]";  
}  

str translate((Formula)`<Expr lhs> is <QualifiedName state>`, Context ctx) {
  str specOfLhs = getSpecTypeName(lhs, ctx.tm);
  str specRel = ctx.rm[lhs@\loc].relExpr; 

  str stateRel = "State<capitalize(specOfLhs)><capitalize(replaceAll("<state>", "::", "__"))>";
  switch ("<state>") {
    case "initialized": stateRel = "initialized";
    case "finalized" : stateRel = "finalized";
  };
  
  str stepRel = (Expr)`<Expr _>'` := lhs ? "nxt" : "cur";
  return "inState[<stepRel>, <specRel><maybeRename(getFieldName(lhs,ctx), "instance")>, <stateRel>]";    
}  

str translate((Formula)`eventually <Formula f>`, Context ctx) {
  str s = ctx.topLevelLtl ? "let cur = first | " : "";
  ctx = flipTopLevelLtl(ctx);
  
  return "<s>(exists cur: (cur[config as cur] |x| *(order + loop))[nxt-\>config] | let step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(f,ctx)>)";
} 

str translate((Formula)`always <Formula f>`, Context ctx) {
  str s = ctx.topLevelLtl ? "let cur = first | " : "";
  ctx = flipTopLevelLtl(ctx);

  return "<s>(forall cur: (cur[config as cur] |x| *(order + loop))[nxt-\>config] | let step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(f,ctx)>)";
}

str translate((Formula)`always-last <Formula f>`, Context ctx) {
  str s = ctx.topLevelLtl ? "let cur = first | " : "";
  ctx = flipTopLevelLtl(ctx);

  return "<s>(forall cur: (cur[config as cur] |x| *(order + loop))[nxt-\>config] - last | let step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(f,ctx)>)";
}

str translate((Formula)`<Formula u> until <Formula r>`, Context ctx) {
  str s = ctx.topLevelLtl ? "let cur = first | " : "";
  ctx = flipTopLevelLtl(ctx);
  
  return "<s>
         '  (((no loop || (exists goal: (cur[config as cur] ⨝ *order)[nxt-\>config] | (let cur = goal, step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(r,ctx)>))) =\>
         '    (exists goal: (cur[config as cur] ⨝ *order)[nxt-\>config] | (let cur = goal, step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | 
         '      (forall cur: ((cur[config-\>cur] ⨝ *order)[nxt-\>config] ∩ (goal[config-\>nxt] ⨝ ^order)[cur-\>config]) | (let step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(u,ctx)>)))))
         '  && ((not (no loop || (exists goal: (cur[config as cur] ⨝ *order)[nxt-\>config] | (let cur = goal, step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(r,ctx)>)))) =\>
         '    (exists goal: (cur[config as cur] ⨝ *(order+loop))[nxt-\>config] | (let cur = goal, step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] |
         '      (forall cur: (((cur[config-\>cur] ⨝ *order)[nxt-\>config] + (goal[config-\>nxt] ⨝ ^order)[cur-\>config]) & (last[config-\>cur] |x| *order)[nxt-\>config]) | (let step = cur[config as cur] |x| (order + loop), nxt = step[nxt-\>config] | <translate(u,ctx)>))))))";
}

str translate((Formula)`next <Formula f>`, Context ctx) {
  str s = ctx.topLevelLtl ? "let cur = first | " : "";
  ctx = flipTopLevelLtl(ctx);
  
  return "<s>(let cur = (cur[config as cur] |x| (order ∪ loop))[nxt-\>config], step = cur[config as cur] |x| (order ∪ loop) | some cur && (<translate(f,ctx)>))";
}

str translate((Formula)`first <Formula f>`, Context ctx) {
  return "let cur = first | <translate(f,ctx)>";
}

str translate((Formula)`<TransEvent event> on <Expr var> <WithAssignments? with>`, Context ctx) {
  str spec = getSpecTypeName(var, ctx.tm); 
  str r = translateRelExpr(var, ctx); 

  if ((TransEvent)`*` := event) {
    return "some (raisedEvent ⨝ <ctx.stepRel> ⨝ <r>)";
  }
  
  set[str] paramConstraints = {};
  str spc = "";
  if (specType(str name) := getType(var,ctx.tm)) {
    spc = name;
  } else {
    throw "Must be of spec type";
  }
  
  for (/(Assignment)`<Id fld> = <Expr val>` <- \with) {
    str paramRel = "(ParamEvent<spc><capitalize("<event>")><capitalize("<fld>")> ⨝ <ctx.stepRel>)[<fld>]";
    
    if (isPrim(val, ctx.tm)) {
      AttRes r = translateAttrExpr(val, ctx);
      paramConstraints += "some ((<paramRel><if (r.rels != {}) {> ⨯ <intercalate(" ⨯ ", [*r.rels])><}>) where (<fld> = <r.constraint>))";
    } else {
      paramConstraints += "<paramRel> = <translateRelExpr(val,ctx)>";
    }    
  }
  
  return "(<for (pc <- paramConstraints) {><pc> ∧ <}>Event<capitalize(spec)><capitalize("<event>")> ⊆ (raisedEvent ⨝ <ctx.stepRel> ⨝ <r>)[event])";
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

str translate((Formula)`<Expr expr> = {}`, Context ctx) = "no <translateRelExpr(expr, ctx)>";
str translate((Formula)`{} = <Expr expr>`, Context ctx) = "no <translateRelExpr(expr, ctx)>";
str translate((Formula)`<Expr expr> = none`, Context ctx) = "no <translateRelExpr(expr, ctx)>";
str translate((Formula)`none = <Expr expr>`, Context ctx) = "no <translateRelExpr(expr, ctx)>";
default str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);

str translate((Formula)`<Expr expr> != {}`, Context ctx) = "some <translateRelExpr(expr, ctx)>";
str translate((Formula)`{} != <Expr expr>`, Context ctx) = "some <translateRelExpr(expr, ctx)>";
str translate((Formula)`<Expr expr> != none`, Context ctx) = "some <translateRelExpr(expr, ctx)>";
str translate((Formula)`none != <Expr expr>`, Context ctx) = "some <translateRelExpr(expr, ctx)>";
default str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\>",  ctx);

str translate((Formula)`if <Formula cond> then <Formula then> else <Formula \else>`,  Context ctx) = translate((Formula)`(<Formula cond> =\> <Formula then>) && (!(<Formula cond>) =\> <Formula \else>)`, ctx);

str translate((Formula)`if <Formula cond> then <Formula then>`,  Context ctx) = translate((Formula)`(<Formula cond> =\> <Formula then>)`, ctx);

str translate((Formula)`noOp(<Expr expr>)`, Context ctx) {
  return "notInChangeSet[step, <ctx.rm[expr@\loc].relExpr><renameIfNecessary(expr, "instance", ctx)>]";
}

default str translate(Formula f, Context ctx) { throw "No translation function implemented yet for `<f>`"; }

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isPrim(lhs, ctx.tm) && isPrim(rhs, ctx.tm)) {
    // it is equality on attributes
    return translateRestrictionEq(lhs, rhs, op, ctx);
  } else {
    return translateRelEq(lhs, rhs, op, ctx);
  }
}

str translateRelEq(Expr lhs, Expr rhs, str op, Context ctx)  
  = "<translateRelExpr(lhs, ctx)> <op> <translateRelExpr(rhs, ctx)><maybeRename(getFieldName(rhs,ctx),getFieldName(lhs,ctx))>";

str translateRestrictionEq(Expr lhs, Expr rhs, str op, Context ctx) {
  AttRes l = translateAttrExpr(lhs, ctx);
  AttRes r = translateAttrExpr(rhs, ctx);

  return "(some (<intercalate(" ⨯ ", [*(l.rels + r.rels)])>) where (<l.constraint> <op> <r.constraint>))";
}  

str translateRelExpr(current:(Expr)`(<Expr e>)`, Context ctx) = "(<translateRelExpr(e,ctx)>)";
str translateRelExpr(current:(Expr)`<Id id>`, Context ctx) = ctx.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr expr>'`, Context ctx) = ctx.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr expr>.<Id field>`, Context ctx) = ctx.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`<Expr spc>[<Id field>]`, Context ctx) = ctx.rm[current@\loc].relExpr;

str translateRelExpr(current:(Expr)`{<Id var> : <Expr expr> | <Formula f>}`, Context ctx) {
  str te = ctx.rm[expr@\loc].relExpr;
  return  "{<var> : <te> | <translate(f,ctx)>}"; 
}

str translateRelExpr(current:(Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = ctx.rm[current@\loc].relExpr; 
str translateRelExpr(current:(Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = ctx.rm[current@\loc].relExpr;
str translateRelExpr(current:(Expr)`{<{Expr ","}* elems>}`  , Context ctx) = ctx.rm[current@\loc].relExpr;

str translateRelExpr(current:(Expr)`this`, Context ctx) = ctx.rm[current@\loc].relExpr;

default str translateRelExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

alias AttRes = tuple[set[str] rels, str constraint];
 
AttRes translateAttrExpr((Expr)`(<Expr e>)`, Context ctx) {
  AttRes r = translateAttrExpr(e, ctx);   
  return <r.rels, "(<r.constraint>)">;
} 

Context replaceCurRel(Context old, str newCurRel) = ctx(old.rm, old.tm, old.allSpecs, old.topLevelLtl, "nxt", old.stepRel, old.nxtUniquePrefix);

AttRes translateAttrExpr((Expr)`<Expr e>'`, Context ctx) {
  AttRes r = translateAttrExpr(e, replaceCurRel(ctx, "nxt"));   
  return <r.rels, "<r.constraint>">;
} 

AttRes translateAttrExpr(current:(Expr)`<Id id>`, Context ctx) {
 str fld = "param_<ctx.nxtUniquePrefix()>_<id>";
 str r = "<ctx.rm[current@\loc].relExpr><renameIfNecessary(current, fld, ctx)>";
 return <{r}, fld>;
}

AttRes translateAttrExpr(current:(Expr)`this.<Id id>`, Context ctx) {
 //str r = "<ctx.rm[current@\loc].relExpr><renameIfNecessary(current, "cur_<id>", ctx)>";
 //return <{r}, "cur_<id>">;
 str r = "<ctx.rm[current@\loc].relExpr><renameIfNecessary(current, "<ctx.curRel>_<id>", ctx)>";
 return <{r}, "<ctx.curRel>_<id>">;
}

AttRes translateAttrExpr(current:(Expr)`<Expr spc>[<Id inst>].<Id fld>`, Context ctx) {
 str fldName = "<inst>_<fld>_<ctx.nxtUniquePrefix()>";
 str r = "<ctx.rm[current@\loc].relExpr><renameIfNecessary(current, fldName, ctx)>";
 return <{r}, fldName>;
}

AttRes translateAttrExpr(current:(Expr)`<Expr expr>.<Id fld>`, Context ctx) {
  str r = ctx.rm[current@\loc].relExpr;

  if (getType(expr, ctx.tm) == stringType() && "<fld>" == "length") {
    str newFld = "<getFieldName(expr,ctx)>_<ctx.nxtUniquePrefix()>";
    r = "<r><renameIfNecessary(expr, newFld, ctx)>";
    return <{r}, "length(<newFld>)">;
  } else {
    IdRole role = getIdRole(expr,ctx.tm);
    str newFld = "<fld>";
    switch (role) {
      case fieldId(): newFld = "<ctx.curRel>_<ctx.nxtUniquePrefix()>_<fld>";
      case paramId(): newFld = "param_<ctx.nxtUniquePrefix()>_<fld>";
      case quantVarId(): newFld = "<expr>_<fld>_<ctx.nxtUniquePrefix()>";
    }
    
    r = "<r><renameIfNecessary(current, newFld, ctx)>";
    return <{r}, newFld>;
  }
}

AttRes translateAttrExpr(current:(Expr)`<Id func>(<{Expr ","}* actuals>)`, Context ctx) {
  str r = ctx.rm[current@\loc].relExpr;
  list[Expr] params = [p | p <- actuals];
  
  switch("<func>") {
    case "substr": {
      str newFld = "<getFieldName(params[0],ctx)>_<ctx.nxtUniquePrefix()>";
      AttRes sub = translateAttrExpr(params[0],ctx);
      AttRes frm = translateAttrExpr(params[1],ctx);
      AttRes to = translateAttrExpr(params[2],ctx);

      r = "<r><renameIfNecessary(params[0], newFld, ctx)>";
      return <{r} + sub.rels + frm.rels + to.rels, "substr(<newFld>,<frm.constraint>,<to.constraint>)">;
    }
    case "toInt": {
      str newFld = "<getFieldName(params[0],ctx)>_<ctx.nxtUniquePrefix()>";
      r = "<r><renameIfNecessary(params[0], newFld, ctx)>";
      AttRes p0 = translateAttrExpr(params[0],ctx);
      return <{r} + p0.rels, "toInt(<p0.constraint>)">;
    }
    case "toStr": {
      str newFld = "<getFieldName(params[0],ctx)>_<ctx.nxtUniquePrefix()>";
      r = "<r><renameIfNecessary(params[0], newFld, ctx)>";
      AttRes p0 = translateAttrExpr(params[0],ctx);
      return <{r} + p0.rels, "toStr(<p0.constraint>)">;
    } 
    default: throw "Unknown function `<func>`";           
  }
}

AttRes translateAttrExpr((Expr)`- <Expr e>`, Context ctx) { 
  AttRes r = translateAttrExpr(e,ctx);
  return <r.rels, "(- <r.constraint>)">;
}

AttRes translateAttrExpr(cur:(Expr)`|<Expr e>|`, Context ctx) { 
  AType tipe = getType(e, ctx.tm);
  AttRes r = translateAttrExpr(e,ctx);

  if (intType() := tipe) {
    return <r.rels, "|<r.constraint>|">;
  } else if (setType(_) := tipe) {
    //return <{ctx.rm[cur@\loc].relExpr}, getFieldName(cur,ctx)>;
    return <{"(<intercalate(" x ", [re | re <- r.rels])>)[count() as size]"}, getFieldName(cur,ctx)>;
  }
  
  throw "Unable to translate `|<e>|` of type `<tipe>`";
}

private AttRes translateBinAttrExpr(Expr lhs, Expr rhs, str op, Context ctx) {
   AttRes l = translateAttrExpr(lhs,ctx);
   AttRes r = translateAttrExpr(rhs,ctx);
   
   return <l.rels + r.rels, "<l.constraint> <op> <r.constraint>">;
}

AttRes translateAttrExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = translateBinAttrExpr(lhs, rhs, "*", ctx);
AttRes translateAttrExpr((Expr)`<Expr lhs> / <Expr rhs>`, Context ctx) = translateBinAttrExpr(lhs, rhs, "/", ctx);
AttRes translateAttrExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = translateBinAttrExpr(lhs, rhs, "+", ctx);
AttRes translateAttrExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = translateBinAttrExpr(lhs, rhs, "-", ctx);
AttRes translateAttrExpr((Expr)`<Expr lhs> % <Expr rhs>`, Context ctx) = translateBinAttrExpr(lhs, rhs, "%", ctx);

AttRes translateAttrExpr(current:(Expr)`{<Id var> : <Expr expr> | <Formula f>}`, Context ctx) {
  str te = ctx.rm[expr@\loc].relExpr;
  return  <{"{<var> : <te> | <translate(f,ctx)>}"}, "">; 
}

AttRes translateAttrExpr((Expr)`<Lit l>`, Context ctx) = <{}, translateLit(l)>;

default AttRes translateAttrExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }


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
  Heading header = ctx.rm[expr@\loc].heading;
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
str getSpecTypeName(Expr expr, TModel tm) = name when optionalType(specType(str name)) := getType(expr, tm);

default str getSpecTypeName(Expr expr, TModel tm) { throw "Expression `<expr>` is not a Spec Type"; }

