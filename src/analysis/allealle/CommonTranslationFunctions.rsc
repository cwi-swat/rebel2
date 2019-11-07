module analysis::allealle::CommonTranslationFunctions

import rebel::lang::SpecSyntax;
import rebel::lang::SpecTypeChecker;

import String;
import Node;
import IO;

data Config = config(rel[Spec spc, str instance, State initialState] instances, 
                     rel[Spec spc, str instance, str field, str val] initialValues, 
                     TModel tm,
                     int numberOfTransitions,
                     int maxSizeIntegerSets = 5);

data State 
  = uninitialized()
  | finalized()
  | state(str name)
  | anyState()
  ;

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
  } else {
    throw "<tipe> is not a (set) spec type";
  }
}

bool isAttributeType(Expr expr, TModel tm) {
  switch (getType(expr, tm)) {
    case intType() : return true;
    default: return false;
  }
}

bool isAttributeType(FormalParam p, TModel tm) {
  switch (getType(p, tm)) {
    case intType() : return true;
    default: return false;
  }
}

str type2Str(intType()) = "int";
default str type2Str(AType t) = "id"; 

str convertType((Type)`Integer`) = "int";
default str convertType(Type t) = "id";

AType getType(Field f, TModel tm) = tm.facts[f.name@\loc] when f.name@\loc in tm.facts;
default AType getType(Field f, TModel tm) { throw "No type info available for `<f>`"; }

AType getType(Expr expr, TModel tm) = tm.facts[expr@\loc] when expr@\loc in tm.facts;
default AType getType(Expr expr, TModel tm) { throw "No type info available for `<expr>` at `<expr@\loc>`"; }

AType getType(FormalParam p, TModel tm) = tm.facts[p.name@\loc] when p.name@\loc in tm.facts;
default AType getType(FormalParam p, TModel tm) { throw "No type info available for `<p>`"; }

AType getType(Type t, TModel tm) = tm.facts[t@\loc] when t@\loc in tm.facts;
default AType getType(Type t, TModel tm) { throw "No type info available for `<t>`"; }

IdRole getIdRole(expr:(Expr)`<Id id>`, TModel tm) = tm.definitions[def].idRole when {loc def} := tm.useDef[id@\loc];
IdRole getIdRole(expr:(Expr)`this.<Id id>`, TModel tm) = tm.definitions[def].idRole when {loc def} := tm.useDef[id@\loc];

default IdRole getIdRole(Expr expr, TModel tm) { throw "Role of identifier `<expr>` can not be found in type model"; }

bool isParam(Expr expr, TModel tm) 
  = getIdRole(expr,tm) == paramId();
default bool isParam(Expr _, TModel _) = false;

Spec getSpecByType(Expr expr, rel[Spec spc, str instance, State initialState] instances, TModel tm) {
  if (specType(str specName) := getType(expr, tm)) {
    return lookupSpecByName(specName, instances);
  }
  
  throw "Expression `<expr>` is not of spec type";
}

//@memo
set[Spec] lookupSpecs(rel[Spec spc, str instance, State initialState] instances) = {i.spc | i <- instances}; 

//@memo
Spec lookupSpecByName(str specName, rel[Spec spc, str instance, State initialState] instances) {
  for (s <- lookupSpecs(instances), "<s.name>" == specName) {
    return s;
  }
  
  throw "Spec `<specName>` could not be found";
}

//@memo 
set[rebel::lang::SpecSyntax::State] lookupStates(Spec spc) 
  = {delAnnotationsRec(st) | /rebel::lang::SpecSyntax::State st <- spc.states, st has name};

//@memo
set[str] lookupStateLabels(Spec spc) 
  = {getStateLabel(spc, st) | rebel::lang::SpecSyntax::State st <- lookupStates(spc)} 
  when str specName := toLowerCase("<spc.name>");

//@memo
set[str] lookupStateLabelsWithDefaultState(Spec spc)
  = lookupStateLabels(spc) + {"state_uninitialized"} + (!isEmptySpec(spc) ? {"state_finalized"} : {});   

str getStateLabel(Spec spc, rebel::lang::SpecSyntax::State state)
  = "state_<getLowerCaseSpecName(spc)>_<toLowerCase("<state>")>";

bool isEmptySpec(Spec spc) = /Field _ !:= spc.fields && /Transition _ !:= spc.states;

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

bool isPrim(Type tipe, TModel tm) = isPrim(t) when tipe@\loc in tm.facts, AType t := tm.facts[tipe@\loc];
bool isPrim(Type tipe, TModel tm) { throw "No type information found for `<tipe>`"; }

bool isPrim(intType()) = true;
bool isPrim(AType _) = false; 

bool isInternalEvent(TransEvent te, Spec s) = isInternalEvent(lookupEventByName("<te>", s), s);
default bool isInternalEvent(TransEvent te, Spec s) { throw "Unable to find event with name `<te>` in `<s.name>`"; }  

bool isInternalEvent(Event e) = /(Modifier)`internal` := e.modi;
