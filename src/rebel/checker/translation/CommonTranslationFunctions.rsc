module rebel::checker::translation::CommonTranslationFunctions

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import rebel::checker::translation::RelationCollector;

import String;
import IO;

data State 
  = uninitialized()
  | finalized()
  | state(str name)
  | anyState()
  | noState()
  ;

alias AlleAlleSnippet = tuple[rel[str,str] typeCons, rel[str,str] fieldMultiplicityCons, rel[str,str] paramMultiplicityCons, rel[str,str] eventPred, map[str,str] transPred, rel[str,str] facts, map[str,str] asserts];

//@memo
str getLowerCaseSpecName(Spec spc) = toLowerCase("<spc.name>");

//@memo
str getCapitalizedSpecName(Spec spc) = capitalize("<spc.name>");

//@memo
str getCapitalizedEventName(Event e) = capitalize("<e.name>");

//@memo
str getCapitalizedParamName(FormalParam p) = capitalize("<p.name>");

//@memo
str getCapitalizedFieldName(Field f) = capitalize("<f.name>");

//@memo
list[str] getInstancesOfType(Type tipe, rel[Spec spc, str instance] instances, TModel tm) 
  = ["<i.instance>" | i <- instances, "<i.spc.name>" == getSpecOfType(tipe, tm)];

str getSpecOfType(Type tipe, TModel tm) {
  if (setType(specType(str spc)) := getType(tipe, tm)) {
    return spc;
  } else if (specType(str spc) := getType(tipe, tm)) {
    return spc;
  } else if (optionalType(specType(str spc)) := getType(tipe, tm)) {
    return spc;
  } else {
    throw "<tipe> is not a (set) spec type";
  }
}

str type2Str(intType()) = "int";
str type2Str(stringType()) = "str";
default str type2Str(AType t) = "id"; 

str convertType((Type)`Integer`) = "int";
str convertType((Type)`String`) = "str";
default str convertType(Type t) = "id";

AType getType(Field f, TModel tm) = tm.facts[f.name@\loc] when f.name@\loc in tm.facts;
default AType getType(Field f, TModel tm) { throw "No type info available for `<f>`"; }

AType getType(Expr expr, TModel tm) = tm.facts[expr@\loc] when expr@\loc in tm.facts;
default AType getType(Expr expr, TModel tm) { throw "No type info available for `<expr>` at `<expr@\loc>`"; }

AType getType(Id id, TModel tm) = tm.facts[id@\loc] when id@\loc in tm.facts;
default AType getType(Id id, TModel tm) { throw "No type info available for `<id>` at `<id@\loc>`"; }

AType getType(FormalParam p, TModel tm) = tm.facts[p.name@\loc] when p.name@\loc in tm.facts;
default AType getType(FormalParam p, TModel tm) { throw "No type info available for `<p>`"; }

AType getType(Type t, TModel tm) = tm.facts[t@\loc] when t@\loc in tm.facts;
default AType getType(Type t, TModel tm) { throw "No type info available for `<t>`"; }

IdRole getIdRole(Expr expr, TModel tm) {
  switch (expr) {
    case c:(Expr)`this`: return getIdRole(c@\loc, tm);
    case (Expr)`<Id id>`: return getIdRole(id@\loc, tm);
    case (Expr)`<Expr expr>.<Id id>`: return getIdRole(id@\loc, tm);
  }
  
  throw "No fetch of Id role defined for `<expr>`";
}

IdRole getIdRole(loc expr, TModel tm) = tm.definitions[def].idRole when {loc def} := tm.useDef[expr];
default IdRole getIdRole(loc expr, TModel tm) { throw "Role can not be found for expression at `<expr>`"; }

bool isParam(Expr expr, TModel tm) 
  = getIdRole(expr,tm) == paramId();
default bool isParam(Expr _, TModel _) = false;

Spec getSpecByType(Expr expr, set[Spec] specs, TModel tm) {
  AType tipe = getType(expr, tm);
  
  if (specType(str specName) := tipe || optionalType(specType(str specName)) := tipe) {
    return lookupSpecByName(specName, specs);
  }
  
  throw "Expression `<expr>` is not of spec type";
}

//@memo
set[Spec] lookupSpecs(rel[Spec spc, str instance, State initialState] instances) = {i.spc | i <- instances}; 

//@memo
private Spec lookupSpecByName(str specName, set[Spec] specs) {
  for (s <- specs, "<s.name>" == specName) {
    return s;
  }
  
  throw "Spec `<specName>` could not be found";
}

set[str] lookupStates(Spec spc, TModel tm) {
  set[str] states = {};
  for (Define d <- tm.defines, d.idRole == stateId(), d.scope == spc@\loc, d.id notin {"initialized","finalized","uninitialized"}) {
    states += d.id;
  }
  
  //println(states);
  return states;
}

//@memo
set[str] lookupStateLabels(Spec spc, TModel tm) = {getStateLabel(spc, st) | str st <- lookupStates(spc,tm)};

//@memo
set[str] lookupStateLabelsWithDefaultStates(Spec spc, TModel tm) {
  set[str] states = lookupStateLabels(spc,tm);
  
  if (/(Transition)`(*) -\> <State _> : <{TransEvent ","}+ _>;` := spc.states) {
    states += "state_uninitialized";
  }
  
  if (/(Transition)`<State _> -\> (*) : <{TransEvent ","}+ _>;` := spc.states) {
    states += "state_finalized";
  } 
  
  return states; 
}

str getStateLabel(Spec spc, str state) = "state_<getLowerCaseSpecName(spc)>_<toLowerCase(state)>";

bool isEmptySpec(Spec spc) = /Transition _ !:= spc.states;

//@memo
set[str] lookupInstances(Spec spc, rel[Spec spc, str instance] instances) 
  = instances[spc];

//@memo
set[str] lookupEventNames(Spec spc)
  = {"event_<specName>_<ev>" | Event event <- lookupEvents(spc), str ev := toLowerCase(replaceAll("<event.name>", "::", "_"))}
  when str specName := toLowerCase("<spc.name>");
  
set[str] lookupRaisableEventName(Spec spc)  
  = {"event_<specName>_<ev>" | Event event <- lookupEvents(spc), !isInternalEvent(event), str ev := toLowerCase(replaceAll("<event.name>", "::", "_"))}
  when str specName := toLowerCase("<spc.name>");

//@memo
set[Event] lookupEvents(Spec spc) = {e | /Event e := spc.events};

//@memo
Event lookupEventByName(str eventName, Spec spc) {
  for (Event e <- lookupEvents(spc), "<e.name>" == eventName) {
    return e;
  }
  
  throw "Event with name `<eventName>` could not be found";
}

//@memo
bool isNonOptionalScalar(Type tipe, TModel tm) = isNonOptionalScalar(t) when tipe@\loc in tm.facts, AType t := tm.facts[tipe@\loc];
default bool isNonOptionalScalar(Type tipe, TModel tm)  { throw "No type information found for `<tipe>`"; }

bool isNonOptionalScalar(setType(_)) = false;
bool isNonOptionalScalar(optionalType(_)) = false;
default bool isNonOptionalScalar(AType _) = true;

bool isSetOfInt(Type tipe, TModel tm) = isSetOfType(tipe, intType(), tm);
bool isSetOfString(Type tipe, TModel tm) = isSetOfType(tipe, stringType(), tm);

bool isSetOfPrim(Type tipe, TModel tm) = isSetOfInt(tipe, tm) || isSetOfString(tipe, tm);

private bool isSetOfType(Type tipe, AType elemType, TModel tm) { 
  if (tipe@\loc notin tm.facts) {
    throw "No type information found for `<tipe>`";
  } 
  
  return setType(elemType) := tm.facts[tipe@\loc];
}

bool isPrim(Type tipe, TModel tm) = isPrim(t) when tipe@\loc in tm.facts, AType t := tm.facts[tipe@\loc];
default bool isPrim(Type tipe, TModel tm) { throw "No type information found for `<tipe>`"; }

bool isPrim(Expr expr, TModel tm) = isPrim(t) when expr@\loc in tm.facts, AType t := tm.facts[expr@\loc];
default bool isPrim(Expr expr, TModel tm) { throw "No type information found for `<expr>` at <expr@\loc>"; }

bool isPrim(intType()) = true;
bool isPrim(stringType()) = true;
default bool isPrim(AType _) = false; 

bool isInternalEvent(TransEvent te, Spec s) = isInternalEvent(lookupEventByName("<te>", s), s);
default bool isInternalEvent(TransEvent te, Spec s) { throw "Unable to find event with name `<te>` in `<s.name>`"; }  

bool isInternalEvent(Event e) = /(Modifier)`internal` := e.modifiers;

