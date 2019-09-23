module analysis::allealle::CommonTranslationFunctions

import lang::Syntax;

import String;
import Node;

data Config = config(rel[Spec spc, str instance, State initialState] instances, 
                     rel[Spec spc, str instance, str field, set[str] val] initialValues, 
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
  = ["<i.instance>" | i <- instances, "<i.spc.name>" == "<tipe>"];

@memo
set[Spec] lookupSpecs(rel[Spec spc, str instance, State initialState] instances) = {i.spc | i <- instances}; 

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
list[Field] lookupNonPrimFields(Spec s) = [f | /Field f <- s.fields, !isPrim(f.tipe)];

@memo
list[Field] lookupPrimFieldsWithOtherMult(Spec s) = [f | /Field f <- s.fields, isPrim(f.tipe), (Multiplicity)`one` !:= f.tipe.mult];

@memo
list[Field] lookupOnePrimitiveFields(Spec s) = [f | /f:(Field)`<Id name> : <Type tipe>` <- s.fields, hasMultOfOne(tipe), isPrim(tipe)];

@memo
list[str] lookupOnePrimitiveFieldNames(Spec s) = ["<f.name>" | Field f <- lookupOnePrimitiveFields(s)];

@memo
list[FormalParam] lookupPrimitiveParams(Event e) = [p | /FormalParam p <- e.params, isPrim(p.tipe)];

@memo
list[FormalParam] lookupNonPrimParams(Event e) = [p | /FormalParam p <- e.params, !isPrim(p.tipe)];

@memo
bool hasMultOfOne((Type)`one <TypeName _>`) = true; 

@memo
default bool hasMultOfOne(Type _) = false;

@memo
bool isPrim(Type t) = isPrim(t.tp);

bool isPrim((TypeName)`Integer`) = true;
default bool isPrim(TypeName _) = false;