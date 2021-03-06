module rebel::checker::translation::EventTranslator

import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::translation::RelationCollector;
import rebel::checker::translation::FormulaAndExpressionTranslator;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import Set;
import List;
import ParseTree;
import analysis::graphs::Graph;

str constructTransitionFunctions(set[Spec] spcs, RelMapping rm, TModel tm) {
  Graph[SyncedWith] syncDep = buildSyncGraph(spcs, tm);
  return "<for (Spec s <- spcs, !isEmptySpec(s)) {>// Transition function for <s.name>
         '<constructTransitionFunction(s, syncDep, spcs, rm, tm)><}>";
}

str constructTransitionFunction(Spec spc, Graph[SyncedWith] syncDep, set[Spec] spcs, RelMapping rm, TModel tm) {
  list[str] getEventParams(Event e) { 
    list[str] actuals = ["step", "inst"];
    
    for (/FormalParam p <- e.params) {
      actuals += "(step ⨝ ParamEvent<getCapitalizedSpecName(spc)><getCapitalizedEventName(e)><getCapitalizedParamName(p)>)[<(isPrim(p.tipe,tm) ? "<p.name>" : "<p.name>-\>instance")>]";
    }

    return actuals;
  }
   
  str buildTransCond(Event e) {
    int lastUnique = 0;
    int nxtUnique() { lastUnique += 1; return lastUnique; }
    Context ctx = ctx(rm, tm, spcs, true, defaultCurRel(), defaultStepRel(), nxtUnique);

    tuple[set[str] names, list[str] syncs] lets = syncedInstanceRels(spc, e, "inst", syncDep, top(), ctx);
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
  
  IdRole role = getIdRole(exp, ctx.tm);
  
  switch(role) {
    case specId(): {
      return [<toLowerCase("<exp>"), "<ctx.rm[exp@\loc].relExpr><renameIfNecessary(exp, "instance", ctx)>">];
    }
    case fieldId(): {
      lrel[str,str] result = [<getLowerCaseSpecName(spc), instRel>];
      result += <"<getLowerCaseSpecName(spc)>_<replaceAll("<exp>",".","_")>", "<ctx.rm[exp@\loc].relExpr><renameIfNecessary(exp, "instance", ctx)>">;
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
      if ({loc def} := ctx.tm.useDef[exp@\loc]) {
        Decl d = findDecl(def);
        return findRootRel(d.expr, instRel, spc, evnt, scp, ctx);
      }
    }
    default: throw "Unknown role `<role>` for expression `<exp>` at `<exp@\loc>`";
  }
}

private tuple[set[str],list[str]] syncedInstanceRels(Spec s, Event e, str instRel, Graph[SyncedWith] syncDep, SyncScope scp, Context c) {
  list[str] syncLets = [];
  set[str] relNames = {};
  
  for (SyncedWith synced <- syncDep[<s,e>]) {
    for (/f:(Formula)`<Expr exp>.<Id ev>(<{Expr ","}* args>)` := e.body, "<ev>" == "<synced.e.name>", getSpecTypeName(exp, c.tm) == "<synced.s.name>") {
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

alias SyncedWith = tuple[Spec s, Event e];

private Graph[SyncedWith] buildSyncGraph(set[Spec] spcs, TModel tm) {
  Spec findSpecByName(str name) = s when Spec s <- spcs, "<s.name>" == name;
  Event findEventByName(str name, Spec s) = e when Event e <- s.events, "<e.name>" == name;

  Graph[SyncedWith] syncDep = {};
   
  for (Spec s <- spcs, Event e <- s.events, /(Formula)`<Expr exp>.<Id ev>(<{Expr ","}* args>)` := e.body,  getIdRole(ev@\loc, tm) in {eventId(), eventVariantId()}, AType tipe := getType(exp,tm), (specType(str spcName) := tipe || optionalType(specType(str spcName)) := tipe)) {
    Spec otherSpec = findSpecByName(spcName);
    Event otherEvent = findEventByName("<ev>", otherSpec);
    
    syncDep += <<s,e>,<otherSpec, otherEvent>>;             
  }
  
  return syncDep;
}

private str toStr(tuple[SyncedWith from, SyncedWith to] n) = "<toStr(from)> -\> <toStr(to)>";
private str toStr(SyncedWith sw) = "<sw.s.name>.<sw.e.name>";

str translateEventsToPreds(set[Spec] spcs, RelMapping rm, TModel tm) {
  str preds = "";
  
  for (Spec s <- spcs) {
    preds += "// Event predicates for <s.name>\n";
    
    for (Event e <- s.events) {
      preds += isFrameEvent(e) ? translateFrameEvent(s, e, getLowerCaseSpecName(s), rm, tm, spcs) : translateEventToPred(s, e, getLowerCaseSpecName(s), rm, tm, spcs);
      preds += "\n";
    }   
  }
  
  return preds;
}

private bool isFrameEvent(Event e) = "<e.name>" == "__frame";

str translateEventToPred(Spec spc, Event event, str instanceRel, RelMapping rm, TModel tm, set[Spec] allSpecs) {
  int lastUnique = 0;
  int nxtUnique() { lastUnique += 1; return lastUnique; }
  Context ctx = ctx(rm, tm, allSpecs, true, defaultCurRel(), defaultStepRel(), nxtUnique);

  list[str] letRels = buildLetVars(spc, event, instanceRel);
  list[str] paramVars = ["step:(cur:id, nxt:id)", "<getLowerCaseSpecName(spc)>: (instance:id)"] + buildParamVars(event, tm);
  
  return "pred event<getCapitalizedSpecName(spc)><getCapitalizedEventName(event)>[<intercalate(", ", paramVars)>]
         '  = let <intercalate(",\n", letRels)> |
         '    <translateEventBody(spc, event, ctx)>
         '";
}

str translateFrameEvent(Spec spc, Event frameEvent, str instRel, RelMapping rm, TModel tm, set[Spec] allSpecs) {
  int lastUnique = 0;
  int nxtUnique() { lastUnique += 1; return lastUnique; }
  Context ctx = ctx(rm, tm, allSpecs, true, defaultCurRel(), defaultStepRel(), nxtUnique);

  list[str] letRels = buildLetVars(spc, frameEvent, instRel);

  return "pred frame<getCapitalizedSpecName(spc)>[step: (cur:id, nxt:id), <getLowerCaseSpecName(spc)>: (instance:id)] 
         '  = let <intercalate(",\n", letRels)> | (
         '    nxtState = curState <if (/Field f := spc.fields) {>∧
         '    (
         '      curState ⊆ uninitialized ∨ 
         '      (<translatePost(frameEvent, ctx)>)
         '    )<}>
         '  )
         '";
}

private list[str] buildLetVars(Spec spc, Event event, str instRel) {
  str renamePrimField(Field f, str prefix) = "<f.name>-\><prefix><getCapitalizedFieldName(f)>";
  list[str] letRels = ["cur = step[cur-\>config]", "nxt = step[nxt-\>config]", "curState = (instanceInState ⨝ cur ⨝ <instRel>)[state]", "nxtState = (instanceInState ⨝ nxt ⨝ <instRel>)[state]"];
  
  return letRels;
}

private list[str] buildParamVars(Event event, TModel tm) {
  list[str] varDefs = [];
  
  for (/FormalParam p <- event.params) {
    varDefs += "<p.name>: (<isPrim(p.tipe,tm) ? "<p.name>" : "instance">:<convertType(p.tipe)>)";
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
  = "<if (cons != []) {>// Preconditions 
    '<intercalate(" ∧\n", cons)><}>"
    when /Pre pre := event, 
         list[str] cons := [translate(f,ctx) | f <- pre.formulas];

private default str translatePre(Event event, Context ctx) = "";     

private str translatePost(Event event, Context ctx) 
  = "<if (cons != []) {>// Postconditions
    '<intercalate(" ∧\n", cons)><}>"
    when /Post post := event,
         list[str] cons := [translate(f,ctx) | f <- post.formulas];

private default str translatePost(Event event, Context ctx) = "";     