module analysis::allealle::CommonTranslationFunctions

import lang::Syntax;
import analysis::Checker;

import String;
import Node;

data Config = config(rel[Spec spc, str instance, State initialState] instances, 
                     rel[Spec spc, str instance, str field, set[str] val] initialValues, 
                     TModel tm,
                     int numberOfTransitions,
                     int maxSizeIntegerSets = 5);

data State 
  = uninitialized()
  | finalized()
  | state(str name)
  ;

@memo
str getLowerCaseSpecName(Spec spc) = toLowerCase("<spc.name>");

@memo
str getCapitalizedSpecName(Spec spc) = capitalize("<spc.name>");

@memo
str getCapitalizedEventName(Event e) = capitalize("<e.name>");

@memo
str getCapitalizedParamName(FormalParam p) = capitalize("<p.name>");

@memo
str getOnePrimStateVectorName(Spec spc) = "SV<getCapitalizedSpecName(spc)>OnePrims";

@memo
str getMultStateVectorName(Spec spc, Field fld) = "SV<getCapitalizedSpecName(spc)><capitalize("<fld.name>")>";

@memo
list[str] getInstancesOfType(Type tipe, rel[Spec spc, str instance] instances)
  = ["<i.instance>" | i <- instances, "<i.spc.name>" == "<tipe.tp>"];

bool isAttributeType(Expr expr, TModel tm) {
  switch (getType(expr, tm)) {
    case intType(oneMult()) : return true;
    default: return false;
  }
}

AType getType(Field f, TModel tm) = tm.facts[f@\loc] when f@\loc in tm.facts;
default AType getType(Field f, TModel tm) { throw "No type info available for `<f>`"; }

AType getType(Expr expr, TModel tm) = tm.facts[expr@\loc] when expr@\loc in tm.facts;
default AType getType(Expr expr, TModel tm) { throw "No type info available for `<expr>`"; }

bool isParam(Expr expr, TModel lookup) 
  = d.idRole == paramId()
  when 
    {loc def} := lookup.useDef[expr@\loc],
    Define d := lookup.definitions[def];

default bool isParam(Expr _, TModel _) = false;

Spec getSpecByType(Expr expr, rel[Spec spc, str instance, State initialState] instances, TModel tm) {
  if (specType(_, str specName) := getType(expr, tm)) {
    return lookupSpecByName(specName, instances);
  }
  
  throw "Expression `<expr>` is not of spec type";
}

@memo
set[Spec] lookupSpecs(rel[Spec spc, str instance, State initialState] instances) = {i.spc | i <- instances}; 

@memo
Spec lookupSpecByName(str specName, rel[Spec spc, str instance, State initialState] instances) {
  for (s <- lookupSpecs(instances), "<s.name>" == specName) {
    return s;
  }
  
  throw "Spec `<specName>` could not be found";
}

@memo 
set[lang::Syntax::State] lookupStates(Spec spc) 
  = {delAnnotationsRec(st) | /lang::Syntax::State st <- spc.states, st has name};

@memo
set[str] lookupStateLabels(Spec spc) 
  = {getStateLabel(spc, st) | lang::Syntax::State st <- lookupStates(spc)} 
  when str specName := toLowerCase("<spc.name>");

@memo
set[str] lookupStateLabelsWithDefaultState(Spec spc)
  = lookupStateLabels(spc) + {"state_uninitialized", "state_finalized"};   

str getStateLabel(Spec spc, lang::Syntax::State state)
  = "state_<getLowerCaseSpecName(spc)>_<toLowerCase("<state>")>";

@memo
set[str] lookupInstances(Spec spc, rel[Spec spc, str instance] instances) 
  = instances[spc];

@memo
set[str] lookupEventNames(Spec spc)
  = {"event_<specName>_<ev>" | Event event <- lookupEvents(spc), str ev := toLowerCase(replaceAll("<event.name>", "::", "_"))}
  when str specName := toLowerCase("<spc.name>");

@memo
set[Event] lookupEvents(Spec spc) = {e | /Event e := spc.events};

@memo
Event lookupEventByName(str eventName, Spec spc) {
  for (Event e <- lookupEvents(spc), "<e.name>" == eventName) {
    return e;
  }
  
  throw "Event with name `<eventName>` could not be found";
}

@memo 
list[Field] lookupNonPrimFields(Spec s, TModel tm) = [f | /Field f <- s.fields, !isPrim(f.tipe, tm)];

@memo 
list[Field] lookupNonPrimFieldsWithOneMult(Spec s, TModel tm) = [f | /Field f <- s.fields, !isPrim(f.tipe, tm) && hasMultOfOne(f.tipe, tm)];

@memo
list[Field] lookupPrimFieldsWithOtherMult(Spec s, TModel tm) = [f | /Field f <- s.fields, isPrim(f.tipe, tm) && !hasMultOfOne(f.tipe, tm)];

@memo
list[Field] lookupOnePrimitiveFields(Spec s, TModel tm) = [f | /f:(Field)`<Id name> : <Type tipe>` <- s.fields, isPrim(tipe, tm) && hasMultOfOne(tipe, tm)];

@memo
list[str] lookupOnePrimitiveFieldNames(Spec s, TModel tm) = ["<f.name>" | Field f <- lookupOnePrimitiveFields(s,tm)];

@memo
list[FormalParam] lookupPrimitiveParams(Event e, TModel tm) = [p | /FormalParam p <- e.params, isPrim(p.tipe,tm) && hasMultOfOne(p.tipe,tm)];

@memo
list[FormalParam] lookupNonPrimParams(Event e, TModel tm) = [p | /FormalParam p <- e.params, !isPrim(p.tipe,tm)];

@memo
bool hasMultOfOne(Type tipe, TModel tm) = hasMultOfOne(t) when tipe@\loc in tm.facts, AType t := tm.facts[tipe@\loc];
default bool hasMultOfOne(Type tipe, TModel _) { throw "No type information found for `<tipe>`"; }

bool hasMultOfOne(AType t) = t.mult == oneMult() when t has mult;
default bool hasMultOfOne(AType t) { throw "Type `<t>` does not have a multiplicity associated with it"; }

@memo
bool isPrim(Type tipe, TModel tm) = isPrim(t) when tipe@\loc in tm.facts, AType t := tm.facts[tipe@\loc];
bool isPrim(Type tipe, TModel tm) { throw "No type information found for `<tipe>`"; }

bool isPrim(intType(_)) = true;
bool isPrim(AType _) = false; 