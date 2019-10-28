module analysis::allealle::EventTranslator

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
  
data Context = ctx(map[str var, str relation] varLookup, void () incNrOfChangedInstances, int () getNrOfChangedInstances, Config cfg);

str constructTransitionFunction(Spec spc, Config cfg) {
  list[str] getEventParams(Event e) { 
    list[str] actuals = ["step", "inst"];
    
    list[FormalParam] params = lookupPrimitiveParams(e, cfg.tm);
    if (params != []) {
      actuals += "(step ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)>Primitives)[<intercalate(",", ["<p.name>" | p <- params])>]";
    }  
    
    for (FormalParam p <- lookupNonPrimParams(e, cfg.tm)) {
      actuals += "(step ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)><capitalize("<p.name>")>)[<p.name>]";
    }

    return actuals;
  }
  
  str buildTransCond(Event e) =
    "(event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)>[<intercalate(",", getEventParams(e))>] ∧
    '(step ⨝ raisedEvent)[event] = Event<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)> ∧
    '(changedInstance ⨝ step)[instance] ⊆  inst) // todo: Needs to be extended for synced events!";
  
  list[str] eventTrans = [buildTransCond(e) | Event e <- lookupEvents(spc), !isFrameEvent(e)];
  
  return "pred possibleTransitions<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id)] 
         '  = ∀ inst ∈ (Instance ⨝ <getCapitalizedSpecName(spc)>)[instance] |
         '    (some inst ∩ ((raisedEvent ⨝ step)[instance]) ⇔ (
         '      <intercalate("\n∨\n", eventTrans)>
         '    ))
         '    ∧
         '    (no inst ∩ (changedInstance ⨝ step)[instance] ⇔ frame<getCapitalizedSpecName(spc)>[step, inst])"; 
}

str translateEventsToPreds(Spec spc, Config cfg) =
  "<for (Event e <- events) {><if (isFrameEvent(e)) {><translateFrameEvent(spc, e, getLowerCaseSpecName(spc), cfg)><} else {><translateEventToPred(spc, e, getLowerCaseSpecName(spc), cfg)><}>
  '<}>"
  when set[Event] events := lookupEvents(spc);

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";

str translateEventToPred(Spec spc, Event event, str instanceRel, Config cfg) {
  list[str] letRels = buildLetVars(spc, event, instanceRel, cfg);
  list[str] paramVars = ["step:(cur:id, nxt:id)", "<getLowerCaseSpecName(spc)>: (instance:id)"] + buildParamVars(event, cfg);
  
  return "pred event<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>[<intercalate(", ", paramVars)>]
         '  = let <intercalate(",\n", letRels)> |
         '    <translateEventBody(spc, event, ctx((), () {;}, int () {return -1;}, cfg))>
         '";
}

str translateSyncedEvent(Spec spc, Event event, str instRel, Context ctx) {
  tuple[list[str] rels, map[str,str] lookup] l = buildLetVars(spc, event, instRel, ctx.cfg);
  ctx.varLookup = l.lookup;
  
  return "// Event <spc.name>.<event.name>
         '(let <intercalate(",\n", l.rels)> |
         '  <translateEventBody(spc, event, ctx)>
         ')";     
}

str translateFrameEvent(Spec spc, Event frameEvent, str instRel, Config cfg) {
  str getNoValues() {
    if (lookupOnePrimitiveFields(spc,cfg.tm) != []) {
      return "(no curFlat)";
    } else {
      return "(<intercalate(" ∨ ", ["(no cur<capitalize(f.name)>)" | Field f <- lookupNonPrimFieldsWithOneMult(spc, cfg.tm)])>)"; 
    }     
  }

  list[str] letRels = buildLetVars(spc, frameEvent, instRel, cfg);
  
  return "pred frame<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id), <getLowerCaseSpecName(spc)>: (instance:id)] 
         '  = let <intercalate(",\n", letRels)> | (
         '    nxtState = curState ∧
         '    (
         '      <getNoValues()> ∨ 
         '      (<translatePost(frameEvent, ctx((), void () {;}, int () {return -1;}, cfg))>)
         '    )
         '  )
         '";
}

private list[str] buildLetVars(Spec spc, Event event, str instRel, Config cfg) {
  str renameFlattenedFields(list[Field] fields, str prefix) =
    intercalate(",", ["<f.name>-\><prefix><capitalize("<f.name>")>" | f <- fields]);

  list[str] tmpRels = [];

  tmpRels += "cur = step[cur-\>config]";
  tmpRels += "nxt = step[nxt-\>config]";
  tmpRels += "curState = (instanceInState ⨝ cur ⨝ <instRel>)[state]";
  tmpRels += "nxtState = (instanceInState ⨝ nxt ⨝ <instRel>)[state]";
  
  list[Field] flattenFields = lookupOnePrimitiveFields(spc, cfg.tm);
  if (flattenFields != []) {
    tmpRels += "curFlat = (<getOnePrimStateVectorName(spc)> ⨝ cur ⨝ <instRel>)[<renameFlattenedFields(flattenFields, "cur")>]";
    tmpRels += "nxtFlat = (<getOnePrimStateVectorName(spc)> ⨝ nxt ⨝ <instRel>)[<renameFlattenedFields(flattenFields, "nxt")>]";
  }
  
  for (Field f <- lookupNonPrimFields(spc, cfg.tm)) {
    tmpRels += "cur<capitalize("<f.name>")> = (cur ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")> ⨝ <instRel>)[<f.name>]";
    tmpRels += "nxt<capitalize("<f.name>")> = (nxt ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")> ⨝ <instRel>)[<f.name>]";      
  }
    
  return tmpRels;
}

private list[str] buildParamVars(Event event, Config cfg) {
  list[str] varDefs = [];
  
  list[FormalParam] params = lookupPrimitiveParams(event, cfg.tm);
  // <getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Flattened = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Primitives)[<intercalate(",", ["<p.name>" | p <- params])>]
  if (params != []) {
    varDefs += "paramFlat: (<intercalate(",", ["<p.name>:<convertType(p.tipe)>" | p <- params])>)";
  }  
  
  // "params<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")> = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")>)[<p.name>]";
  for (FormalParam p <- lookupNonPrimParams(event, cfg.tm)) {
    varDefs += "param<getCapitalizedParamName(p)>: (<p.name>:id)";
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

str translate((Formula)`<Expr spc>.<Id event>(<{Expr ","}* params>)`, Context ctx) { 
  // inline synced event
  str relOfSync = translate(spc, ctx);

  str getFieldName(Expr expr) = visit(expr) {
    case (Expr)`this.<Id field>`: return "<field>";
    case (Expr)`<Id field>`: return "<field>";
  };
  
  //ctx.addChangedInstance("<relOfSync>[<getFieldName(spc)>-\>instance]");
  ctx.incNrOfChangedInstances();
  
  Spec syncedSpec = getSpecByType(spc, ctx.cfg.instances, ctx.cfg.tm);
  Event syncedEvent = lookupEventByName("<event>", syncedSpec);
  
  // Fix synced event param values
  list[str] paramConst = [];
  list[FormalParam] formals = [p | FormalParam p <- syncedEvent.params];
  list[Expr] args = [a | Expr a <- params];
   
  for (int i <- [0..size(formals)]) {
    if (isAttributeType(args[i],ctx.cfg.tm) && isAttributeType(formals[i], ctx.cfg.tm)) {
      list[str] refRels = findReferencedRels(findReferences(args[i], ctx), ctx) +
                          "(o ⨝ ParamsEvent<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)>Primitives)[<formals[i].name>-\>s_<formals[i].name>]";
      
      paramConst += "(some (<intercalate(" ⨯ ", refRels)>) where <translateAttr(args[i],ctx)> = s_<formals[i].name>)"; 
    } else {
      paramConst += "<translate(args[i],ctx)> = (o ⨝ ParamsEvent<getCapitalizedSpecName(syncedSpec)><getCapitalizedEventName(syncedEvent)><capitalize("<formals[i].name>")>)[<formals[i].name>-\><getFieldName(args[i])>]";
    }
  }
   
  return "// Synchronised with `<syncedSpec.name>.<syncedEvent.name>` event
         '<if (paramConst != []) {>// Constrain input param values of synced event 
         '<for (c <- paramConst) {><c> ∧
         '<}><}>
         '<translateSyncedEvent(syncedSpec, syncedEvent, "<relOfSync>[<getFieldName(spc)>-\>instance]", ctx)>";
}  

str translate(f: (Formula)`<Expr lhs> is <Id state>`, Context ctx) {
  str specOfLhs = getType(lhs, ctx.cfg.tm).name;
   
  str specRel = isParam(lhs, ctx.cfg.tm) ?
    "(<ctx.varLookup["param_<lhs>"]>[<lhs>-\>instance] ⨯ o[cur-\>config])" : 
    "(o[cur -\> config] ⨯ (Instance ⨝ <capitalize(specOfLhs)>))";  
  
  str stateRel = "<state>" == "initialized" ?
    "initialized" :
    "State<capitalize(specOfLhs)><capitalize("<state>")>";
    
  return "(<specRel> ⨝ instanceInState)[state] ⊆ <stateRel>";    
} 

str translate((Formula)`<Formula lhs> && <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∧ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> || <Formula rhs>`,    Context ctx) = "(<translate(lhs,ctx)> ∨ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> =\> <Formula rhs>`,   Context ctx) = "(<translate(lhs,ctx)> ⇒ <translate(rhs,ctx)>)";
str translate((Formula)`<Formula lhs> \<=\> <Formula rhs>`, Context ctx) = "(<translate(lhs,ctx)> ⇔ <translate(rhs,ctx)>)";

str translate((Formula)`<Expr lhs> = <Expr rhs>`,   Context ctx)  = translateEq(lhs, rhs, "=", ctx);
str translate((Formula)`<Expr lhs> != <Expr rhs>`,   Context ctx) = translateEq(lhs, rhs, "!=", ctx);

str translate((Formula)`<Expr lhs> \< <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\<",  ctx);
str translate((Formula)`<Expr lhs> \<= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\<=", ctx);
str translate((Formula)`<Expr lhs> \>= <Expr rhs>`, Context ctx) = translateRestrictionEquality(lhs, rhs, "\>=", ctx);
str translate((Formula)`<Expr lhs> \> <Expr rhs>`,  Context ctx) = translateRestrictionEquality(lhs, rhs, "\>",  ctx);

str translateEq(Expr lhs, Expr rhs, str op, Context ctx) {
  // Is it equality on attributes?
  if (isAttributeType(lhs, ctx.cfg.tm) && isAttributeType(rhs, ctx.cfg.tm)) {
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
  
  list[str] refRels = findReferencedRels(r, ctx);

  return "(some (<intercalate(" ⨯ ", refRels)>) where (<translateAttr(lhs,ctx)> <operator> <translateAttr(rhs,ctx)>))";
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

list[str] findReferencedRels(set[Reference] refs, Context ctx) {
  list[str] refRels = [];
  
  if (cur() in refs) {
    refRels += "curFlat"; //ctx.varLookup["cur_flattened"];
  }
  if (next() in refs) {
    refRels += "nxtFlat"; //ctx.varLookup["nxt_flattened"];
  }
  if (param() in refs) {
    refRels += "paramFlat"; //ctx.varLookup["params_flattened"];
  }
  
  return refRels; 
}
  
str translate((Expr)`(<Expr e>)`, Context ctx) = "(<translate(e,ctx,prefix)>)"; 
str translate((Expr)`<Id id>`, Context ctx) = "param<capitalize(id)>";
str translate((Expr)`this.<Id id>`, Context ctx) = "cur<capitalize("<id>")>[<id>]";
str translate((Expr)`this.<Id id>'`, Context ctx) = "nxt<capitalize("<id>")>[<id>]";

str translateAttr((Expr)`(<Expr e>)`, Context ctx) = "(<translateAttr(e,ctx,prefix)>)"; 
str translateAttr((Expr)`<Id id>`, Context ctx) = "<id>";
str translateAttr((Expr)`this.<Id id>`, Context ctx) = "cur<capitalize("<id>")>";
str translateAttr((Expr)`this.<Id id>'`, Context ctx) = "nxt<capitalize("<id>")>";

str translateAttr((Expr)`now`, Context ctx) { throw "Not yet supported"; }
str translateAttr((Expr)`<Lit l>`, Context ctx) = translate(l);

str translateAttr((Expr)`- <Expr e>`, Context ctx) = "-<translateAttr(e,ctx)>";
str translateAttr((Expr)`<Expr lhs> * <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  *  <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> \\ <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)> \\ <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> + <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  +  <translateAttr(rhs,ctx)>";
str translateAttr((Expr)`<Expr lhs> - <Expr rhs>`, Context ctx) = "<translateAttr(lhs,ctx)>  -  <translateAttr(rhs,ctx)>";

default str translate(Expr e, Context ctx) { throw "Can not translate expression `<e>` at location <e@\loc>"; }

str translate((Lit)`<Int i>`) = "<i>";
str translate((Lit)`<StringConstant s>`) { throw "Not yet supported"; }
