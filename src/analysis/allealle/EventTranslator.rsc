module analysis::allealle::EventTranslator

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::SyncedEventGraphBuilder;
import analysis::allealle::RelationCollector;
import analysis::allealle::FormulaAndExpressionTranslator;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import IO;
import Set;
import List;
import Map;
import ParseTree;
import util::Maybe;

str constructTransitionFunction(Spec spc, Graph[SyncedWith] syncDep, Config cfg) {
  list[str] getEventParams(Event e) { 
    list[str] actuals = ["step", "inst"];
    
    for (/FormalParam p <- e.params) {
      actuals += "(step ⨝ ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)><getCapitalizedParamName(p)>)[<(isPrim(p.tipe,cfg.tm) ? "<p.name>" : "<p.name>-\>instance")>]";
    }

    return actuals;
  }
   
  str buildTransCond(Event e) {
    int lastParam = 0;
    str nxtParam() { lastParam += 1; return "param_<lastParam>"; }
    Context c = ctx(cfg, defaultCurRel(), defaultStepRel(), nxtParam);

    tuple[set[str] names, list[str] syncs] lets = syncedInstanceRels(spc, e, "inst", syncDep, top(), c);
    lets.names += {"inst"};
    if (lets.syncs != []) lets.syncs = ["cur = step[cur-\>config]"] + lets.syncs;
    
    return "(event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)>[<intercalate(",", getEventParams(e))>] ∧
           '(step ⨝ raisedEvent)[event] = Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)> ∧
           '<if (lets.syncs != []) {>let <intercalate(", ", dup(lets.syncs))> | <}>changeSetCanContain[step, <intercalate(" ∪ ", [*lets.names])>])";
  }
  
  list[str] eventTrans = [buildTransCond(e) | Event e <- lookupEvents(spc), !isFrameEvent(e), !isInternalEvent(e)];
  
  return "pred possibleTransitions<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id)] 
         '  = ∀ inst ∈ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] |
         '    <if (eventTrans != []) {>(some inst ∩ ((raisedEvent ⨝ step)[instance]) ⇔ (
         '      <intercalate("\n∨\n", eventTrans)>
         '    ))
         '    ∧<}>
         '    (notInChangeSet[step, inst] ⇒ frame<getCapitalizedSpecName(spc)>[step, inst])
         '"; 
}

private data SyncScope 
  = top()
  | scope(str inst, Spec s, Event e, map[str,Expr] actuals, SyncScope parent)
  ;

lrel[str fieldName, str relName] findRootRel(Expr exp, str instRel, Spec spc, Event evnt, SyncScope scp, Context ctx) {
  Decl findDecl(loc locOfVar) {
    visit(evnt.body) {
      case cur:(Decl)`<{Id ","}+ vars> : <Expr expr>`: { 
        for (Id var <- vars) {
          if (var@\loc == locOfVar) {
            return cur;
          } 
        }
      }
    }
    throw "Unable to find binding decl";
  }
  
  IdRole role = getIdRole(exp, ctx.cfg.tm);
  
  switch(role) {
    case fieldId(): {
      lrel[str,str] result = [<getLowerCaseSpecName(spc), instRel>];
      result += <getLowerCaseSpecName(spc), "<ctx.cfg.rm[exp@\loc].relExpr><renameIfNecessary(exp, "instance", ctx)>">;
      return result;  
    }
    case paramId(): { 
      str fieldName = "<exp>";
      if (top() := scp) {
        return [<fieldName, "(ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(evnt)><capitalize(fieldName)> ⨝ step)[<fieldName> -\> instance]">];
      } else if (scope(str inst, Spec s, Event e, map[str,Expr] actuals, SyncScope parent) := scp, fieldName in actuals) {  
        return findRootRel(actuals[fieldName], inst, s, e, parent, ctx);
      } else {
        throw "Can not resolve parameter `<fieldName>` in `<spc.name>.<evnt.name>`"; 
      }
    }
    case quantVarId(): {
      if ({loc def} := ctx.cfg.tm.useDef[exp@\loc]) {
        Decl d = findDecl(def);
        return findRootRel(d.expr, instRel, spc, evnt, scp, ctx);
      }
    }
  } 
}

private tuple[set[str],list[str]] syncedInstanceRels(Spec s, Event e, str instRel, Graph[SyncedWith] syncDep, SyncScope scp, Context c) {
  list[str] syncLets = [];
  set[str] relNames = {};
  
  for (SyncedWith synced <- syncDep[<s,e>]) {
    for (/f:(Formula)`<Expr exp>.<Id ev>(<{Expr ","}* args>)` := e.body, "<ev>" == "<synced.e.name>", getSpecTypeName(exp, c.cfg.tm) == "<synced.s.name>") {
      lrel[str,str] root = findRootRel(exp, instRel, s, e, scp, c); 
      
      str newInstRel = "";
      for (<str varName, str relExpr> <- root) {
        syncLets += "<varName> = <relExpr>";
        relNames += varName;
        newInstRel = varName;
      }      
      
      if (<n,sl> := syncedInstanceRels(synced.s, synced.e, newInstRel, syncDep, scope(newInstRel, s, e, ("<fp.name>":arg | /FormalParam fp <- synced.e.params, Expr arg <- args), scp), c)) {
        syncLets += sl;
        relNames += n;
      } 
    }    
  }
  
  return <relNames, syncLets>;
}

str translateEventsToPreds(Spec spc, Config cfg) =
  "<for (Event e <- events) {><if (isFrameEvent(e)) {><translateFrameEvent(spc, e, getLowerCaseSpecName(spc), cfg)><} else {><translateEventToPred(spc, e, getLowerCaseSpecName(spc), cfg)><}>
  '<}>"
  when set[Event] events := lookupEvents(spc);

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";

str translateEventToPred(Spec spc, Event event, str instanceRel, Config cfg) {
  int lastParam = 0;
  str nxtParam() { lastParam += 1; return "param_<lastParam>"; }
  Context c = ctx(cfg, defaultCurRel(), defaultStepRel(), nxtParam);
  
  list[str] letRels = buildLetVars(spc, event, instanceRel, cfg);
  list[str] paramVars = ["step:(cur:id, nxt:id)", "<getLowerCaseSpecName(spc)>: (instance:id)"] + buildParamVars(event, c);
  
  return "pred event<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>[<intercalate(", ", paramVars)>]
         '  = let <intercalate(",\n", letRels)> |
         '    <translateEventBody(spc, event, c)>
         '";
}

str translateFrameEvent(Spec spc, Event frameEvent, str instRel, Config cfg) {
  int lastParam = 0;
  str nxtParam() { lastParam += 1; return "param_<lastParam>"; }
  Context c = ctx(cfg, defaultCurRel(), defaultStepRel(), nxtParam);
  
  list[str] letRels = buildLetVars(spc, frameEvent, instRel, cfg);

  return "pred frame<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id), <getLowerCaseSpecName(spc)>: (instance:id)] 
         '  = let <intercalate(",\n", letRels)> | (
         '    nxtState = curState <if (/Field f := spc.fields) {>∧
         '    (
         '      curState ⊆ uninitialized ∨ 
         '      (<translatePost(frameEvent, c)>)
         '    )<}>
         '  )
         '";
}

private list[str] buildLetVars(Spec spc, Event event, str instRel, Config cfg) {
  str renamePrimField(Field f, str prefix) = "<f.name>-\><prefix><getCapitalizedFieldName(f)>";
  list[str] letRels = ["cur = step[cur-\>config]", "nxt = step[nxt-\>config]", "curState = (instanceInState ⨝ cur ⨝ <instRel>)[state]", "nxtState = (instanceInState ⨝ nxt ⨝ <instRel>)[state]"];
  
  return letRels;
}

private list[str] buildParamVars(Event event, Context ctx) {
  list[str] varDefs = [];
  
  for (/FormalParam p <- event.params) {
    varDefs += "<p.name>: (<isPrim(p.tipe,ctx.cfg.tm) ? "<p.name>" : "instance">:<convertType(p.tipe)>)";
  }
  
  return varDefs;
} 

private str translateEventBody(Spec spc, Event event, Context ctx) {
  str pre = translatePre(event, ctx);
  str post = translatePost(event, ctx);

  return  "( 
          '  <pre> <if (pre != "") {> ∧ <}>
          '  <post> <if (post != "") {> ∧ <}>
          '  // Generic event conditions
          '  forceState[curState, nxtState, Event<getCapitalizedSpecName(spc)><capitalize("<event.name>")>] ∧
          '  // Make sure this instance is in the change set
          '  inChangeSet[step, <getLowerCaseSpecName(spc)>]
          ')";
}

private str translatePre(Event event, Context ctx) 
  = "// Preconditions 
    '<intercalate(" ∧\n",[translate(f,ctx) | f <- pre.formulas])>"
    when /Pre pre := event;

private default str translatePre(Event event, Context ctx) = "";     

private str translatePost(Event event, Context ctx) 
  = "// Postconditions
    '<intercalate(" ∧\n", [translate(f, ctx) | Formula f <- post.formulas])>"
    when /Post post := event;

private default str translatePost(Event event, Context ctx) = "";     

//str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";
//str translate((Formula)`!<Formula f>`, Context ctx) = "¬ (<translate(f,ctx)>)";
//
//str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { 
//  str relOfSync = translateRelExpr(spc, ctx);
//  
//  Spec syncedSpec = getSpecByType(spc, ctx.cfg.instances, ctx.cfg.tm);
//  Event syncedEvent = lookupEventByName("<event>", syncedSpec);
//
//  // Fix synced event param values
//  list[str] actuals = ["step", "<relOfSync><maybeRename(getFieldName(spc,ctx), "instance")>"];
//  
//  list[FormalParam] formals = [p | FormalParam p <- syncedEvent.params];
//  list[Expr] args = [a | Expr a <- params];
//   
//  for (int i <- [0..size(formals)]) {
//    switch (args[i]) {
//      case (Expr)`<Int ii>`: actuals += "__IntConst_<ii>[const_<ii>-\><formals[i].name>]"; 
//      case (Expr)`<StringConstant s>`: actuals += "__StrConst_<unquote(s)>[const_<unquote(s)>-\><formals[i].name>]";
//      default: actuals += "<translateRelExpr(args[i], ctx)><maybeRename(getFieldName(args[i], ctx), isPrim(formals[i].tipe,ctx.cfg.tm) ? "<formals[i].name>" : "instance")>";
//    }
//  }
//   
//  return "event<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)>[<intercalate(", ", actuals)>]";  
//}  
//
//private str maybeRename(str orig, str renameAs) = "[<orig> as <renameAs>]" when orig != renameAs;
//private default str maybeRename(str orig, str renameAs) = "";
//
//str getSpecTypeName(Expr expr, TModel tm) = name when specType(str name) := getType(expr, tm);
//default str getSpecTypeName(Expr expr, TModel tm) { throw "Expression `<expr>` is not a Spec Type"; }
//
//str translate((Formula)`<Expr lhs> is <Id state>`, Context ctx) {
//  str specOfLhs = getSpecTypeName(lhs, ctx.cfg.tm);
//  str specRel = ctx.cfg.rm[lhs@\loc].relExpr; 
//  str stateRel = "<state>" == "initialized" ?
//    "initialized" :
//    "State<capitalize(specOfLhs)><capitalize("<state>")>";
//    
//  return "inState[cur, <specRel>, <stateRel>]";    
//} 
//
//str translate((Formula)`forall <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
//  = "(∀ <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";
//
//str translate((Formula)`exists <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
//  = "(exists <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";
//
//str translate(current:(Decl)`<{Id ","}+ ids>: <Expr expr>`, Context ctx) {
//  str te = translateRelExpr(expr, ctx);
//  return intercalate(",", ["<name> ∈ <te>" | Id name <- ids]); 
//} 
//
//str translate((Formula)`<Expr lhs> in <Expr rhs>`,    Context ctx) = "some (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)>-\><getFieldName(rhs,ctx)>])";
//str translate((Formula)`<Expr lhs> notin <Expr rhs>`, Context ctx) = "no (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)>-\><getFieldName(rhs,ctx)>])";
//
//str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∧ <translate(rhs,ctx)>)";
//str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∨ <translate(rhs,ctx)>)";
//str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "(<translate(lhs,ctx)> ⇒ <translate(rhs,ctx)>)";
//str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "(<translate(lhs,ctx)> ⇔ <translate(rhs,ctx)>)";
//
//str translate((Formula)`<Expr exp> = {}`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
//str translate((Formula)`{} = <Expr exp>`, Context ctx) = "no <translateRelExpr(exp, ctx)>";
//default str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);
//default str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);
//
//str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\<",  ctx);
//str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\<=", ctx);
//str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEq(lhs, rhs, "\>=", ctx);
//str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEq(lhs, rhs, "\>",  ctx);
//
//str translate((Formula)`if <Formula cond> then <Formula then> else <Formula \else>`,  Context ctx) = translate((Formula)`(<Formula cond> =\> <Formula then>) && (!(<Formula cond>) =\> <Formula \else>)`, ctx);
//
//str translate((Formula)`noOp(<Expr expr>)`, Context ctx) {
//  return "notInChangeSet[step, <ctx.cfg.rm[expr@\loc].relExpr><renameIfNecessary(expr, "instance", ctx)>]";
//}
//
//default str translate(Formula f, Context ctx) { throw "No translation function implemented yet for `<f>`"; }
//
//str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
//  // Is it equality on attributes?
//  if (isPrim(lhs, ctx.cfg.tm) && isPrim(rhs, ctx.cfg.tm)) {
//    // it is equality on attributes
//    return translateRestrictionEq(lhs, rhs, op, ctx);
//  } else {
//    return translateRelEq(lhs, rhs, op, ctx);
//  }
//}
//
//str translateRelEq(Expr lhs, Expr rhs, str op, Context ctx)  
//  = "<translateRelExpr(lhs, ctx)> <op> <translateRelExpr(rhs, ctx)><maybeRename(getFieldName(rhs,ctx),getFieldName(lhs,ctx))>";
//
//str translateRestrictionEq(Expr lhs, Expr rhs, str operator, Context ctx) {
//  set[str] findReferencedRels(Expr expr) {
//    set[loc] done = {};
//    set[str] rels = {}; 
//    
//    top-down visit(expr) {
//      // We only want fields and parameters
//      case current:(Expr)`<Expr exp>'`: {
//        RelExpr r = ctx.cfg.rm[current@\loc];
//        rels += prefix(r, "nxt");
//        done += exp@\loc;
//      }
//      case current:(Expr)`<Expr exp>.<Id fld>`: {
//        RelExpr r = ctx.cfg.rm[current@\loc];
//        if ((Expr)`this` := exp && current@\loc notin done) {
//          rels += prefix(r, "cur");
//        } else if(getIdRole(exp@\loc,ctx.cfg.tm) == paramId()) {
//          rels += prefix(r, "param");
//        }
//      }
//      case current:(Expr)`<Id id>`: {
//        if (getIdRole(current@\loc,ctx.cfg.tm) == paramId()) {
//          RelExpr r = ctx.cfg.rm[current@\loc];
//          rels += prefix(r, "param");
//        } 
//      }
//    }
//    
//    return rels;
//  }
//
//  set[str] refRels = findReferencedRels(lhs) + findReferencedRels(rhs);
//  return "(some (<intercalate(" ⨯ ", [*refRels])>) where (<translateAttrExpr(lhs,ctx)> <operator> <translateAttrExpr(rhs,ctx)>))";
//}  
//
//str prefix(RelExpr r, str prefix) {
//  if (size(r.heading) > 1) {
//    throw "Can only prefix an unary relation";
//  }
//  
//  str fld = getOneFrom(r.heading);
//  return "<r.relExpr><maybeRename(fld, "<prefix>_<fld>")>";
//}
//
//str translateRelExpr(current:(Expr)`(<Expr e>)`, Context ctx) = "(<translateRelExpr(e,ctx)>)";
//str translateRelExpr(current:(Expr)`<Id id>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//str translateRelExpr(current:(Expr)`<Expr expr>'`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//str translateRelExpr(current:(Expr)`<Expr expr>.<Id field>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//str translateRelExpr(current:(Expr)`<Expr spc>[<Id field>]`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//
//str translateRelExpr(current:(Expr)`{<Id var> : <Expr expr> | <Formula f>}`, Context ctx) {
//  str te = ctx.cfg.rm[expr@\loc].relExpr;
//  return  "{<var> : <te> | <translate(f,ctx)>}"; 
//}
//
//str translateRelExpr(current:(Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr; 
//str translateRelExpr(current:(Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//str translateRelExpr(current:(Expr)`{<{Expr ","}* elems>}`, Context ctx) = ctx.cfg.rm[current@\loc].relExpr;
//
//default str translateRelExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }
//
//str translateAttrExpr((Expr)`(<Expr e>)`,              Context ctx) = "(<translateAttrExpr(e,ctx)>)"; 
//str translateAttrExpr((Expr)`<Id id>`,                 Context ctx) = "param_<id>";
//str translateAttrExpr((Expr)`this.<Id id>`,            Context ctx) = "cur_<id>";
//str translateAttrExpr((Expr)`this.<Id id>'`,           Context ctx) = "nxt_<id>";
//str translateAttrExpr((Expr)`<Expr expr>.<Id fld>`,    Context ctx) = "<fld>";
//str translateAttrExpr((Expr)`<Lit l>`,                 Context ctx) = translateLit(l);
//str translateAttrExpr((Expr)`- <Expr e>`,              Context ctx) = "- <translateAttrExpr(e,ctx)>";
//str translateAttrExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> * <translateAttrExpr(rhs,ctx)>";
//str translateAttrExpr((Expr)`<Expr lhs> / <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> / <translateAttrExpr(rhs,ctx)>";
//str translateAttrExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> + <translateAttrExpr(rhs,ctx)>";
//str translateAttrExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> - <translateAttrExpr(rhs,ctx)>";
//
//default str translateAttrExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }
//
//str translateLit((Lit)`<Int i>`) = "<i>";
//str translateLit((Lit)`<StringConstant s>`) = "<s>";
//
//str renameIfNecessary(Expr expr, str renamed, Context ctx) {
//  str origName = getFieldName(expr,ctx);
//  if (origName != renamed) {
//    return "[<origName> as <renamed>]";
//  } else {
//    return "";
//  }
//}
//
//str getFieldName(Expr expr, Context ctx) {
//  Heading header = ctx.cfg.rm[expr@\loc].heading;
//  if (size(header) > 1) {
//    throw "More than 1 attribute in the relation, unable to determine field name";
//  }
//  
//  return getOneFrom(header); 
//}

