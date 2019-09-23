module analysis::allealle::DynamicRelationsTranslator

import lang::Syntax;
import analysis::allealle::CommonTranslationFunctions;

import String;
import Set;
import List;
import IO;

str translateConfigState(Spec spc, uninitialized()) = "state_uninitialized";
str translateConfigState(Spec spc, finalized())     = "state_finalized";
str translateConfigState(Spec spc, state(str name)) = "state_<toLowerCase("<spc.name>")>_<name>";

str translateDynamicPart(Config config) {
  str def = "// Dynamic configuration of state machines
            '<buildConfigRels(config.numberOfTransitions)>
            '<buildInstanceRel(config.instances)>
            '<buildInstanceInStateRel(config.instances, config.numberOfTransitions)>
            '<buildRaisedEventsRel(config.instances<0,1>, config.numberOfTransitions)>
            '<buildChangedInstancesRel(config.instances<1>, config.numberOfTransitions)>
            '<buildStateVectors(lookupSpecs(config.instances), config.instances<0,1>, config.initialValues, config.numberOfTransitions)>
            '<buildEventParamRels(lookupSpecs(config.instances), config.instances<0,1>, config.numberOfTransitions)>"; 

  return def;
}

private str buildEventParamRels(set[Spec] specs, rel[Spec spc, str instance] instances, int numberOfTransitions)
  = "<for (s <- specs, e <- lookupEvents(s)) {><buildEventSingleParamRel(s,e,numberOfTransitions)>
    '<buildBinRelParamRels(s,e,instances,numberOfTransitions)>
    '<}>";

private str buildEventSingleParamRel(Spec s, Event e, int numberOfTransitions)
 = "ParamsEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)>Primitives (cur:id, nxt:id, <intercalate(",", [toLowerCase("<p.name>:<convertType(p.tipe)>") | p <- params])>) \<= {<buildParamTuples(numberOfTransitions, size(params))>}"
 when 
  list[FormalParam] params := lookupPrimitiveParams(e), 
  size(params) > 0;

private default str buildEventSingleParamRel(Spec _, Event _, int _) = "";
  
private str buildParamTuples(int numberOfTransitions, int numberOfPrimFields) 
  = intercalate(",", ["\<c<c>,c<c+1>,<fields>\>" | int c <- [1..numberOfTransitions]])
  when str fields := intercalate(",", ["?" | int i <- [0..numberOfPrimFields]]);

private str buildBinRelParamRels(Spec s, Event e, rel[Spec spc, str instance] instances, int numberOfTransitions)
  = "<for (FormalParam p <- lookupNonPrimParams(e)) {>ParamsEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)><capitalize("<p.name>")> (cur:id, nxt:id, <toLowerCase("<p.name>")>:id) \<= {<intercalate(",", ["\<c<c>,c<c+1>,<i>\>" | int c <- [1..numberOfTransitions+1], str i <- getInstancesOfType(p.tipe, instances)])>} 
    '<}>";

private str buildStateVectors(set[Spec] specs, rel[Spec spc, str instance] instances, rel[Spec spc, str instance, str field, set[str] val] initialValues, int numberOfTransitions)
  = "<for (Spec s <- specs) {>
    '<buildPrimOneStateVector(s, instances, initialValues, numberOfTransitions)>
    '<buildBinaryStateVectorRels(s, instances, initialValues, numberOfTransitions)><}>"; 

private str buildPrimOneStateVector(Spec s, rel[Spec spc, str instance] instances, rel[Spec spc, str instance, str field, set[str] val] initialValues, int numberOfTransitions)
  = "<getOnePrimStateVectorName(s)> (config:id, instance:id, <buildFieldDecls(fields)>) <buildInitialStateVectorTuples(s, lookupInstances(s, instances), initialValues[s], fields, numberOfTransitions)>"
  when list[Field] fields := lookupOnePrimitiveFields(s); 

private str buildInitialStateVectorTuples(Spec s, set[str] instances, {}, list[Field] fields, int numberOfTransitions) 
  = "\<= {<buildInitialStateVectorUpperBound(instances, size(fields), numberOfTransitions)>}";

private default str buildInitialStateVectorTuples(Spec s, set[str] instances, rel[str instance, str field, set[str] val] initialValues, list[Field] order, int numberOfTransitions)
  = "\>= {<buildInitialStateVectorTuplesPerInstance(initialValues, order)>} \<= {<buildInitialStateVectorUpperBound(instances, size(order), numberOfTransitions)>}";

private str buildInitialStateVectorUpperBound(set[str] instances, int numberOfPrimitiveFields, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<primFields>\>" | int c <- [1..numberOfTransitions+1], str i <- instances])
  when str primFields := intercalate(",", ["?" | int i <- [0..numberOfPrimitiveFields]]);

private str buildInitialStateVectorTuplesPerInstance(rel[str instance, str field, set[str] val] initialValues, list[Field] order) 
  = intercalate(",", ["\<c1,<i>,<buildInitialStateVectorFieldValues(initialValues[i], order)>\>" | str i <- initialValues<0>]); 

private str buildInitialStateVectorFieldValues(rel[str field, set[str] val] initialValues, list[Field] order)
  = intercalate(",", ["<v>" | f <- order, result := initialValues["<f.name>"], str v := (result == {} ? "?" : getOneFrom(getOneFrom(result)))]);

private str buildBinaryStateVectorRels(Spec spc, rel[Spec spc, str instance] instances, rel[Spec spc, str instance, str field, set[str] val] initialValues, int numberOfTransitions) 
  = "<for (f <- binFields) {><getMultStateVectorName(spc,f)> (config:id, instance:id, <toLowerCase("<f.name>")>:id) <buildBinRelBoundsDecl(spc, f, instances, initialValues, numberOfTransitions)>
    '<}>" 
  when list[Field] binFields := lookupNonPrimFields(spc);

private str buildBinRelBoundsDecl(Spec spc, Field f, rel[Spec spc, str instance] instances, {}, int numberOfTransitions) 
  = "\<= {<buildBinRelUpperBounds(spc,f,instances,numberOfTransitions)>}";

private default str buildBinRelBoundsDecl(Spec spc, Field f, rel[Spec spc, str instance] instances, rel[str instance, str field, set[str] val] initialValues, int numberOfTransitions) 
  = "\>= {<buildBinRelLowerBounds(spc,f,initialValues)>} \<= {<buildBinRelUpperBounds(spc,f,instances,numberOfTransitions)>}";

private str buildBinRelLowerBounds(Spec spc, Field f, rel[str instance, str field, set[str] val] initialValues)
  = "TODO";
  
private str buildBinRelUpperBounds(Spec spc, Field f, rel[Spec spc, str instance] instances, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<t>\>" | int c <- [1..numberOfTransitions+1], str i <- inst, str t <- instOfType])
  when 
    set[str] inst := lookupInstances(spc, instances),
    list[str] instOfType := getInstancesOfType(f.tipe, instances);
      
private str buildFieldDecls(list[Field] fields) 
  = intercalate(", ", ["<f.name>:<convertType(f.tipe)>" | Field f <- fields]);
  
private str convertType((Type)`<Multiplicity _> Integer`) = "int";
private default str convertType(Type t) = "id";

private str buildChangedInstancesRel(set[str] instances, int numberOfTransitions) 
  = "changedInstance (cur:id, nxt:id, instance:id) \<= {<intercalate(",", ["\<c<c>,c<c+1>,<i>\>" | int c <- [1..numberOfTransitions], str i <- instances])>}";
  
private str buildRaisedEventsRel(rel[Spec spc, str instance] instances, int numberOfTransitions) 
  = "raisedEvent (cur:id, nxt:id, event:id, instance:id) \<= {<intercalate(",", [buildRaisedEventsTuples(spc, i, numberOfTransitions) | <spc, i> <- instances])>}";

private str buildRaisedEventsTuples(Spec spc, str instance, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,c<c+1>,<event>,<instance>\>" | int c <- [1..numberOfTransitions], str event <- lookupEventNames(spc)]);

private str buildConfigRels(int numberOfTransitions)
  = "Config (config:id) \>= {\<c1\>} \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    'order (cur:id, nxt:id) \<= {<intercalate(",", ["\<c<i>,c<i+1>\>" | int i <- [1..numberOfTransitions]])>}
    'InitialConfig (config:id) = {\<c1\>}
    '";

private str buildInstanceRel(rel[Spec spc, str instance, State initialState] instances)
  = "Instance (spec:id, instance:id) = {<intercalate(",", ["\<<toLowerCase("<inst.spc.name>")>,<inst.instance>\>" | inst <- instances])>}";
  
private str buildInstanceInStateRel(rel[Spec spc, str instance, State state] instances, int numberOfTransitions) 
  = "instanceInState (config:id, instance:id, state:id) \>= {<buildInitialInstanceInStateTuples(instances)>}\<= {<buildInstanceInStateTuples(instances<spc,instance>, numberOfTransitions)>}";

private str buildInitialInstanceInStateTuples(rel[Spec spc, str instance, State state] instances)
  = intercalate(",", ["\<c1,<i>,<translateConfigState(s, st)>\>" | <s,i,st> <- instances]);

private str buildInstanceInStateTuples(rel[Spec spc, str instance] instances, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<st>\>" | int c <- [1..numberOfTransitions+1], <s,i> <- instances, str st <- lookupStateLabelsWithDefaultState(s)]);
  