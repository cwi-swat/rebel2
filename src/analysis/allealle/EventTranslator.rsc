module analysis::allealle::EventTranslator

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::SyncedEventGraphBuilder;
import rebel::lang::SpecSyntax;
import rebel::lang::SpecTypeChecker;

import String;
import IO;
import Set;
import List;
import Map;
import ParseTree;

alias RelHeader = map[str attName, str attDomain];

data Context = ctx(RelHeader (loc) lookupHeader, void (loc, RelHeader) addHeader, Config cfg);

str constructTransitionFunction(Spec spc, Graph[SyncedWith] syncDep, Config cfg) {
  list[str] getEventParams(Event e) { 
    list[str] actuals = ["step", "inst"];
    
    for (/FormalParam p <- e.params) {
      actuals += "(step ⨝ ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)><getCapitalizedParamName(p)>)[<p.name>]";
    }

    return actuals;
  }
  
  str buildTransCond(Event e) {
    tuple[set[str] names, list[str] syncs] lets = syncedInstanceRels(spc, e, "inst", syncDep, top(), cfg);
    lets.names += {"inst"};
    if (lets.syncs != []) lets.syncs = ["cur = step[cur-\>config]"] + lets.syncs;
    
    return "(event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)>[<intercalate(",", getEventParams(e))>] ∧
           '(step ⨝ raisedEvent)[event] = Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)> ∧
           '<if (lets.syncs != []) {>let <intercalate(", ", dup(lets.syncs))> | <}>(changedInstance ⨝ step)[instance] ⊆ <intercalate(" ∪ ", [*lets.names])>)";
  }
  
  list[str] eventTrans = [buildTransCond(e) | Event e <- lookupEvents(spc), !isFrameEvent(e), !isInternalEvent(e)];
  
  return "pred possibleTransitions<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id)] 
         '  = ∀ inst ∈ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] |
         '    <if (eventTrans != []) {>(some inst ∩ ((raisedEvent ⨝ step)[instance]) ⇔ (
         '      <intercalate("\n∨\n", eventTrans)>
         '    ))
         '    ∧<}>
         '    (no inst ∩ (changedInstance ⨝ step)[instance] ⇒ frame<getCapitalizedSpecName(spc)>[step, inst])
         '"; 
}

private data SyncScope 
  = top()
  | scope(str inst, Spec s, Event e, map[str,Expr] actuals, SyncScope parent)
  ;

tuple[str fieldName, str relName] findRootRel(Expr exp, str instRel, Spec spc, Event evnt, SyncScope scp, Context ctx) {
  Decl findDecl(loc locOfVar) {
    visit(e.body) {
      case cur:(Decl)`<{Id ","}+ vars> : <Expr expr>`: { 
        if (Id var <- vars, var@\loc == locOfVar) {
          return cur; 
        }
      }
    }
    throw "Unable to find binding decl";
  }
  
  translateRelExpr(exp, ctx);
  str fieldName = getFieldName(exp, ctx);
  IdRole role = getIdRole(exp, ctx.cfg.tm);
  
  switch(role) {
    case fieldId(): return <fieldName,"(<getCapitalizedSpecName(spc)><capitalize(fieldName)> ⨝ cur ⨝ <instRel>)[<fieldName> -\> instance]">;
    case paramId(): { 
      if (top() := scp) {
        return <fieldName, "(ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(evnt)><capitalize(fieldName)> ⨝ step)[<fieldName> -\> instance]">;
      } else if (scope(str inst, Spec s, Event e, map[str,Expr] actuals, SyncScope parent) := scp, fieldName in actuals) {  
        return findRootRel(actuals[fieldName], inst, s, e, parent, ctx);
      } else {
        throw "Can not resolve parameter `<fieldName>` in `<spc.name>.<evnt.name>`"; 
      }
    }
    case quantVarId(): {
      if ({loc def} := cfg.tm.useDef[exp@\loc]) {
        Decl d = findDecl(def);
        return findRootRel(d.expr);
      }
    }
  } 
}

private tuple[set[str],list[str]] syncedInstanceRels(Spec s, Event e, str instRel, Graph[SyncedWith] syncDep, SyncScope scp, Config cfg) {
  map[loc,RelHeader] rl = ();
  RelHeader lookupHeader(loc expr) = rl[expr] when expr in rl; 
  default RelHeader lookupHeader(loc expr) { throw "Expression location not in rel header map"; }
  void addHeader(loc expr, RelHeader header) { rl += (expr:header); }
  Context c = ctx(lookupHeader, addHeader, cfg);

  list[str] syncLets = [];
  set[str] relNames = {};
  
  for (SyncedWith synced <- syncDep[<s,e>]) {
    for (/f:(Formula)`<Expr exp>.<Id ev>(<{Expr ","}* args>)` := e.body, "<ev>" == "<synced.e.name>", getSpecTypeName(exp,cfg.tm) == "<synced.s.name>") {
      tuple[str fieldName, str relName] root = findRootRel(exp, instRel, s, e, scp, c); 

      syncLets += "<root.fieldName> = <root.relName>";
      relNames += root.fieldName;      
      
      if (<n,sl> := syncedInstanceRels(synced.s, synced.e, root.fieldName, syncDep, scope(root.fieldName, s, e, ("<fp.name>":arg | /FormalParam fp <- synced.e.params, Expr arg <- args), scp), cfg)) {
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
  map[loc,RelHeader] rl = ();
  RelHeader lookupHeader(loc expr) = rl[expr] when expr in rl; 
  default RelHeader lookupHeader(loc expr) { throw "Expression at `<expr>` not in rel header map"; }
  void addHeader(loc expr, RelHeader header) { rl += (expr:header); }
  
  list[str] letRels = buildLetVars(spc, event, instanceRel, cfg);
  list[str] paramVars = ["step:(cur:id, nxt:id)", "<getLowerCaseSpecName(spc)>: (instance:id)"] + buildParamVars(event, cfg);
  
  return "pred event<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>[<intercalate(", ", paramVars)>]
         '  = let <intercalate(",\n", letRels)> |
         '    <translateEventBody(spc, event, ctx(lookupHeader, addHeader, cfg))>
         '";
}

str translateFrameEvent(Spec spc, Event frameEvent, str instRel, Config cfg) {
  map[loc,RelHeader] rl = ();
  RelHeader lookupHeader(loc expr) = rl[expr] when expr in rl; 
  default RelHeader lookupHeader(loc expr) { throw "Expression location not in rel header map"; }
  void addHeader(loc expr, RelHeader header) { rl += (expr:header); }

  list[str] letRels = buildLetVars(spc, frameEvent, instRel, cfg);

  return "pred frame<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id), <getLowerCaseSpecName(spc)>: (instance:id)] 
         '  = let <intercalate(",\n", letRels)> | (
         '    nxtState = curState ∧
         '    (
         '      curState ⊆ uninitialized ∨ 
         '      (<translatePost(frameEvent, ctx(lookupHeader, addHeader, cfg))>)
         '    )
         '  )
         '";
}

private list[str] buildLetVars(Spec spc, Event event, str instRel, Config cfg) {
  str renamePrimField(Field f, str prefix) = "<f.name>-\><prefix><getCapitalizedFieldName(f)>";
  list[str] letRels = ["cur = step[cur-\>config]", "nxt = step[nxt-\>config]", "curState = (instanceInState ⨝ cur ⨝ <instRel>)[state]", "nxtState = (instanceInState ⨝ nxt ⨝ <instRel>)[state]"];
  
  for (/Field f <- spc.fields) {
    str relName = "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)>";

    letRels += "cur<getCapitalizedFieldName(f)> = (cur ⨝ <relName> ⨝ <instRel>)<if (isPrim(f.tipe,cfg.tm)) {>[<renamePrimField(f, "cur")>]<} else {>[<f.name>]<}>";
    letRels += "nxt<getCapitalizedFieldName(f)> = (nxt ⨝ <relName> ⨝ <instRel>)<if (isPrim(f.tipe,cfg.tm)) {>[<renamePrimField(f, "nxt")>]<} else {>[<f.name>]<}>";
  }    

  return letRels;
}

private list[str] buildParamVars(Event event, Config cfg) {
  list[str] varDefs = [];
  
  for (/FormalParam p <- event.params) {
    varDefs += "<p.name>: (<p.name>:<convertType(p.tipe)>)";
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
          '  <getLowerCaseSpecName(spc)> ⊆ (changedInstance ⨝ step)[instance]
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

str translate((Formula)`(<Formula f>)`, Context ctx) = "(<translate(f,ctx)>)";

str getFieldName(Expr expr, Context ctx) {
  RelHeader header = ctx.lookupHeader(expr@\loc);
  if (size(header) > 1) {
    throw "More than 1 attribute in the relation, unable to determine field name";
  }
  
  return getOneFrom(header); 
}

str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { 
  str relOfSync = translateRelExpr(spc, ctx);
  
  Spec syncedSpec = getSpecByType(spc, ctx.cfg.instances, ctx.cfg.tm);
  Event syncedEvent = lookupEventByName("<event>", syncedSpec);

  // Fix synced event param values
  list[str] actuals = ["step", "<relOfSync><maybeRename(getFieldName(spc,ctx), "instance")>"];
  
  list[FormalParam] formals = [p | FormalParam p <- syncedEvent.params];
  list[Expr] args = [a | Expr a <- params];
   
  for (int i <- [0..size(formals)]) {
    if ((Expr)`<Int ii>` := args[i]) {
      actuals += "__C<ii>[val-\><formals[i].name>]"; 
    } else {
      actuals += "<translateRelExpr(args[i], ctx)><maybeRename(getFieldName(args[i], ctx), "<formals[i].name>")>";
    }
  }
   
  return "event<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)>[<intercalate(", ", actuals)>]";  
}  

private str maybeRename(str orig, str renameAs) = "[<orig> as <renameAs>]" when orig != renameAs;
private default str maybeRename(str orig, str renameAs) = "";

str getSpecTypeName(Expr expr, TModel tm) = name when specType(str name) := getType(expr, tm);
default str getSpecTypeName(Expr expr, TModel tm) { throw "Expression `<expr>` is not a Spec Type"; }

str translate((Formula)`<Expr lhs> is <Id state>`, Context ctx) {
  str specOfLhs = getSpecTypeName(lhs, ctx.cfg.tm);
  
  translateRelExpr(lhs, ctx);
  str fieldName = getFieldName(lhs,ctx);
   
  str specRel = isParam(lhs, ctx.cfg.tm) ?
    "<fieldName>[<fieldName>-\>instance]" : 
    "cur<capitalize(fieldName)>[<fieldName>-\>instance]";  
  
  str stateRel = "<state>" == "initialized" ?
    "initialized" :
    "State<capitalize(specOfLhs)><capitalize("<state>")>";
    
  return "inState[cur, <specRel>, <stateRel>]";    
} 

str translate((Formula)`forall <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(forall <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate((Formula)`exists <{Decl ","}+ decls> | <Formula form>`, Context ctx) 
  = "(exists <intercalate(",", [translate(d,ctx) | Decl d <- decls])> | <translate(form,ctx)>)";

str translate((Decl)`<{Id ","}+ ids>: <Expr expr>`, Context ctx) 
  = intercalate(",", ["<name>:<te><maybeRename(getFieldName(expr,ctx),"<name>")>" | Id name <- ids])
  when str te := translateRelExpr(expr, ctx); 

str translate((Formula)`<Expr lhs> in <Expr rhs>`,    Context ctx) = "some (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)> -\> <getFieldName(rhs,ctx)>])";
str translate((Formula)`<Expr lhs> notin <Expr rhs>`, Context ctx) = "no (<translateRelExpr(rhs,ctx)> ∩ <translateRelExpr(lhs,ctx)>[<getFieldName(lhs,ctx)> -\> <getFieldName(rhs,ctx)>])";

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

default str translate(Formula f, Context ctx) { throw "No translation function implemented yet for `<f>`"; }

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isAttributeType(lhs, ctx.cfg.tm) && isAttributeType(rhs, ctx.cfg.tm)) {
    // it is equality on attributes
    return translateRestrictionEq(lhs, rhs, op, ctx);
  } else {
    return translateRelEq(lhs, rhs, op, ctx);
  }
}

str translateRelEq(Expr lhs, Expr rhs, str op, Context ctx) 
  = "<translateRelExpr(lhs, ctx)> <op> <translateRelExpr(rhs, ctx)><maybeRename(getFieldName(rhs,ctx),getFieldName(lhs,ctx))>"; 

str translateRestrictionEq(Expr lhs, Expr rhs, str operator, Context ctx) {
  set[str] findReferencedRels(Expr expr, Context ctx) {
    set[str] rels = {};
    set[loc] nr = {};
  
    top-down visit(expr) {
      case (Expr)`this.<Id field>` : {if (field@\loc notin nr) rels += "cur<capitalize("<field>")>";} 
      case (Expr)`this.<Id field>'`: {rels += "nxt<capitalize("<field>")>"; nr += field@\loc;}
      case (Expr)`<Id param>`      : rels += "<param>";  // event param is referenced
    }
    
    return rels;
  }

  set[str] refRels = findReferencedRels(lhs, ctx) + findReferencedRels(rhs, ctx);

  return "(some (<intercalate(" ⨯ ", [*refRels])>) where (<translateAttrExpr(lhs,ctx)> <operator> <translateAttrExpr(rhs,ctx)>))";
}  

str translateRelExpr(current:(Expr)`(<Expr e>)`, Context ctx) {
  str res = translateRelExpr(e,ctx);
  ctx.addHeader(current@\loc, ctx.lookupHeader(e@\loc));
  
  return  "(<res>)"; 
}

str translateRelExpr(current:(Expr)`<Id id>`, Context ctx) {
  ctx.addHeader(current@\loc, ("<id>": type2Str(getType(current,ctx.cfg.tm))));
  return "<id>";
}

str translateRelExpr(current:(Expr)`this.<Id id>`, Context ctx) { 
  ctx.addHeader(current@\loc, ("<id>": type2Str(getType(current,ctx.cfg.tm))));
  return "cur<capitalize("<id>")>";
}

str translateRelExpr(current:(Expr)`this.<Id id>'`, Context ctx) {
  ctx.addHeader(current@\loc, ("<id>": type2Str(getType(current,ctx.cfg.tm))));
  return "nxt<capitalize("<id>")>";
}

str translateRelExpr(current:(Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = translateSetRelExpr(current@\loc, lhs, rhs, "+", ctx); 
str translateRelExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = translateSetRelExpr(current@\loc, lhs, rhs, "-", ctx);
default str translateRelExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

private str translateSetRelExpr(loc current, Expr lhs, Expr rhs, str op, Context ctx) {
  str lhsRes = translateRelExpr(lhs,ctx);
  str rhsRes = translateRelExpr(rhs,ctx);
  
  str lhsFieldName = getFieldName(lhs, ctx);
  str rhsFieldName = getFieldName(rhs, ctx);
  ctx.addHeader(current, (lhsFieldName : type2Str(getType(lhs, ctx.cfg.tm))));
  
  return "(<lhsRes> <op> (<rhsRes><maybeRename(rhsFieldName, lhsFieldName)>))";
}

str translateAttrExpr((Expr)`(<Expr e>)`, Context ctx) = "(<translateAttrExpr(e,ctx,prefix)>)"; 
str translateAttrExpr((Expr)`<Id id>`, Context ctx) = "<id>";
str translateAttrExpr((Expr)`this.<Id id>`, Context ctx) = "cur<capitalize("<id>")>";
str translateAttrExpr((Expr)`this.<Id id>'`, Context ctx) = "nxt<capitalize("<id>")>";

str translateAttrExpr((Expr)`now`, Context ctx) { throw "Not yet supported"; }
str translateAttrExpr((Expr)`<Lit l>`, Context ctx) = translateLit(l);

str translateAttrExpr((Expr)`- <Expr e>`, Context ctx) = "-<translateAttrExpr(e,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> * <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> \\ <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> \\ <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> + <translateAttrExpr(rhs,ctx)>";
str translateAttrExpr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttrExpr(lhs,ctx)> - <translateAttrExpr(rhs,ctx)>";

default str translateAttrExpr(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

str translateLit((Lit)`<Int i>`) = "<i>";
str translateLit((Lit)`<StringConstant s>`) = "<s>";
