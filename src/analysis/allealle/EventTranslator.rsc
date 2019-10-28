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

//pred eventTailerConnected[step: (cur:id, nxt:id), tailer: (instance:id)]
//  = let cur = step[cur->config],
//        nxt = step[nxt->config],
//        curPrims = (SVTailerOnePrims ⨝ cur ⨝ tailer)[nrOfHits->curNrOfHits], 
//        nxtPrims = (SVTailerOnePrims ⨝ nxt ⨝ tailer)[nrOfHits->nxtNrOfHits] | 
//    (some (curPrims ⨯ nxtPrims) where (nxtNrOfHits = curNrOfHits))    
//  ∧ forceState[(instanceInState ⨝ tailer ⨝ cur)[state], (instanceInState ⨝ tailer ⨝ nxt)[state], EventTailerConnected]
//  ∧ tailer ⊆ (changedInstance ⨝ step)[instance]

str translateEventToPred(Spec spc, Event event, Config cfg) {
    
}

str translateEvent(Spec spc, Event event, str instRel, Config cfg, bool topLevel = true) {
  int nrOfChangedInstances = 1; 
  
  void inc() { nrOfChangedInstances += 1;};
  int get() { return nrOfChangedInstances;};
  
  tuple[list[str] rels, map[str,str] lookup] l = buildLetAndVarLookup(spc, event, instRel, cfg);
  
  return "// Event <spc.name>.<event.name>
         '(let <intercalate(",\n", l.rels)> |
         '  <translateEventBody(spc, event, ctx(l.lookup, inc, get, cfg))>
         ')";     
}

str translateSyncedEvent(Spec spc, Event event, str instRel, Context ctx) {
  tuple[list[str] rels, map[str,str] lookup] l = buildLetAndVarLookup(spc, event, instRel, ctx.cfg);
  ctx.varLookup = l.lookup;
  
  return "// Event <spc.name>.<event.name>
         '(let <intercalate(",\n", l.rels)> |
         '  <translateEventBody(spc, event, ctx, topLevel=false)>
         ')";     
}

str translateFrameEvent(Spec spc, Event frameEvent, str instRel, Config cfg) {
  tuple[list[str] rels, map[str,str] lookup] l = buildLetAndVarLookup(spc, frameEvent, instRel, cfg);

  str getNoValues() {
    if ("cur_flattened" in l.lookup) {
      return "(no <l.lookup["cur_flattened"]>)";
    } else {
      return "(<intercalate(" ∨ ", ["(no <l.lookup["cur_<f.name>"]>)" | Field f <- lookupNonPrimFieldsWithOneMult(spc, cfg.tm)])>)"; 
    }     
  }

  return "// Frame values if needed
         'let <intercalate(",\n", l.rels)> | (
         '  // State must stay the same
         '  <l.lookup["nxt_state"]> = <l.lookup["cur_state"]>
         '  ∧
         '  (
         '    <getNoValues()> ∨ 
         '    (  
         '      <translatePost(frameEvent, ctx(l.lookup, void () {;}, int () {return 1;}, cfg))>
         '    )
         '  )  
         ')";
}

private tuple[list[str], map[str,str]] buildLetAndVarLookup(Spec spc, Event event, str instRel, Config cfg) {
  str renameFlattenedFields(list[Field] fields, str prefix) =
    intercalate(",", ["<f.name>-\><prefix><capitalize("<f.name>")>" | f <- fields]);

  list[str] tmpRels = [];
  map[str,str] varMapping = ();

  // first generate needed relational variables
  tmpRels += "thisInst = <instRel>";
 
  tmpRels += "cur<getCapitalizedSpecName(spc)>State = (instanceInState ⨝ o[cur-\>config] ⨝ thisInst)[state]";
  tmpRels += "nxt<getCapitalizedSpecName(spc)>State = (instanceInState ⨝ o[nxt-\>config] ⨝ thisInst)[state]";
  
  varMapping += ("cur_state": "cur<getCapitalizedSpecName(spc)>State", 
                 "nxt_state": "nxt<getCapitalizedSpecName(spc)>State");  
  
  list[Field] flattenFields = lookupOnePrimitiveFields(spc, cfg.tm);
  if (flattenFields != []) {
    tmpRels += "cur<getCapitalizedSpecName(spc)>Flattened = (<getOnePrimStateVectorName(spc)> ⨝ o[cur -\> config] ⨝ thisInst)[<renameFlattenedFields(flattenFields, "cur")>]";
    tmpRels += "nxt<getCapitalizedSpecName(spc)>Flattened = (<getOnePrimStateVectorName(spc)> ⨝ o[nxt -\> config] ⨝ thisInst)[<renameFlattenedFields(flattenFields, "nxt")>]";
  
    varMapping += ("cur_flattened": "cur<getCapitalizedSpecName(spc)>Flattened",
                   "nxt_flattened": "nxt<getCapitalizedSpecName(spc)>Flattened");
  }
  
  for (Field f <- lookupNonPrimFields(spc, cfg.tm)) {
    tmpRels += "cur<getCapitalizedSpecName(spc)><capitalize("<f.name>")> = (o[cur -\> config] ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")> ⨝ thisInst)[<f.name>]";
    tmpRels += "nxt<getCapitalizedSpecName(spc)><capitalize("<f.name>")> = (o[nxt -\> config] ⨝ SV<getCapitalizedSpecName(spc)><capitalize("<f.name>")> ⨝ thisInst)[<f.name>]";    
  
    varMapping += ("cur_<f.name>": "cur<getCapitalizedSpecName(spc)><capitalize("<f.name>")>",
                   "nxt_<f.name>": "nxt<getCapitalizedSpecName(spc)><capitalize("<f.name>")>");  
  }
  
  list[FormalParam] params = lookupPrimitiveParams(event, cfg.tm);
  for (params != []) {
    tmpRels += "param<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Flattened = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Primitives)[<intercalate(",", ["<p.name>" | p <- params])>]";
    varMapping += ("params_flattened": "param<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>Flattened");
  }  
  
  for (FormalParam p <- lookupNonPrimParams(event, cfg.tm)) {
    tmpRels += "params<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")> = (o ⨝ ParamsEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")>)[<p.name>]";
    varMapping += ("param_<p.name>" : "params<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)><capitalize("<p.name>")>"); 
  }
  
  return <tmpRels, varMapping>;
}

private str translateEventBody(Spec spc, Event event, Context ctx, bool topLevel = true) {
  str pre = translatePre(event, ctx);
  str post = translatePost(event, ctx);

  return  "( 
          '  <pre> <if (pre != "") {> ∧ <}>
          '  <post> <if (post != "") {> ∧ <}>
          '  <translateGenericPart(spc, event, topLevel, ctx)>
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

private str translateGenericPart(Spec spc, Event event, bool topLevel, Context ctx)
  = "// Generic event conditions
    '// Force the instance to go to the correct next state
    '<ctx.varLookup["nxt_state"]> = (<ctx.varLookup["cur_state"]>[state as from] ⨝ (allowedTransitions ⨝ <eventName>))[to-\>state] ∧
    '// Make sure this instance is in the change set
    'thisInst ⊆ (changedInstance ⨝ o)[instance]
    '<if (topLevel){>// Make sure the right event is raised
    '∧ (o ⨝ raisedEvent)[event] = <eventName> ∧ 
    '// Make sure that the changed instance set only contains as many tuples as where asserted as beign members 
    'some (changedInstance ⨝ o)[instance][count() as nci] where nci = <ctx.getNrOfChangedInstances()>
    '<}>"
  when str eventName := "Event<getCapitalizedSpecName(spc)><capitalize("<event.name>")>"; 
    //'(changedInstance ⨝ o)[instance] = <intercalate(" ∪ ", [*changedInstances])><}>"

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
    refRels += ctx.varLookup["cur_flattened"];
  }
  if (next() in refs) {
    refRels += ctx.varLookup["nxt_flattened"];
  }
  if (param() in refs) {
    refRels += ctx.varLookup["params_flattened"];
  }
  
  return refRels; 
}
  
str translate((Expr)`(<Expr e>)`, Context ctx) = "(<translate(e,ctx,prefix)>)"; 
str translate((Expr)`<Id id>`, Context ctx) = "<ctx.varLookup["param_<id>"]>[<id>]";
str translate((Expr)`this.<Id id>`, Context ctx) = "<ctx.varLookup["cur_<id>"]>[<id>]";
str translate((Expr)`this.<Id id>'`, Context ctx) = "<ctx.varLookup["nxt_<id>"]>[<id>]";

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

str translate((Lit)`<Int i>`) = "<i>";
str translate((Lit)`<StringConstant s>`) { throw "Not yet supported"; }
