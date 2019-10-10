module analysis::allealle::DynamicRelationsTranslator

import lang::Syntax;
import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;

import String;
import Set;
import List;
import IO;

str translateConfigState(Spec spc, uninitialized()) = "state_uninitialized";
str translateConfigState(Spec spc, finalized())     = "state_finalized";
str translateConfigState(Spec spc, state(str name)) = "state_<toLowerCase("<spc.name>")>_<name>";

str translateDynamicPart(Config cfg) {
  str def = "// Dynamic configuration of state machines
            '<buildConfigRels(cfg.numberOfTransitions)>
            '<buildInstanceRel(cfg.instances)>
            '<buildInstanceInStateRel(cfg.instances, cfg.numberOfTransitions)>
            '<buildRaisedEventsRel(cfg.instances<0,1>, cfg.numberOfTransitions)>
            '<buildChangedInstancesRel(cfg.instances<1>, cfg.numberOfTransitions)>
            '<buildStateVectors(lookupSpecs(cfg.instances), cfg)>
            '<buildEventParamRels(lookupSpecs(cfg.instances), cfg)>"; 

  return def;
}

private str buildEventParamRels(set[Spec] specs, Config cfg) {
  list[str] rels = [];
  
  for (Spec s <- specs, e <- lookupEvents(s)) {
    rels += buildEventFlattenedParamRel(s,e,cfg);
    rels += buildOtherParamRels(s,e,cfg);
  }
  
  return intercalate("\n", [r | r <- rels, r != ""]);
}

private str buildEventFlattenedParamRel(Spec s, Event e, Config cfg) 
 = "ParamsEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)>Primitives (cur:id, nxt:id, <intercalate(",", [toLowerCase("<p.name>:<convertType(p.tipe)>") | p <- params])>) \<= {<buildParamTuples(cfg.numberOfTransitions, size(params))>}"
 when 
  list[FormalParam] params := lookupPrimitiveParams(e, cfg.tm), 
  size(params) > 0;

private default str buildEventFlattenedParamRel(Spec _, Event _, Config _) = "";
  
private str buildParamTuples(int numberOfTransitions, int numberOfPrimFields) 
  = intercalate(",", ["\<c<c>,c<c+1>,<fields>\>" | int c <- [1..numberOfTransitions]])
  when str fields := intercalate(",", ["?" | int i <- [0..numberOfPrimFields]]);

private str buildOtherParamRels(Spec s, Event e, Config cfg) {
  list[str] rels = [];
  
  for (FormalParam p <- lookupNonPrimParams(e,cfg.tm)) {
    rels += "ParamsEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)><capitalize("<p.name>")> (cur:id, nxt:id, <toLowerCase("<p.name>")>:id) \<= {<intercalate(",", ["\<c<c>,c<c+1>,<i>\>" | int c <- [1..cfg.numberOfTransitions+1], str i <- getInstancesOfType(p.tipe, cfg.instances<0,1>)])>}";  
  }
  
  return intercalate("\n", rels);
}

private str buildStateVectors(set[Spec] specs, Config cfg) //rel[Spec spc, str instance] instances, rel[Spec spc, str instance, str field, set[str] val] initialValues, int numberOfTransitions)
  = "<for (Spec s <- specs) {>
    '<buildFlattenedStateVector(s, cfg)>
    '<buildOtherStateVectorRels(s, cfg)><}>"; 

private str buildFlattenedStateVector(Spec s, Config cfg) {
  list[Field] fields = lookupOnePrimitiveFields(s, cfg.tm);
      
  return "<getOnePrimStateVectorName(s)> (config:id, instance:id, <buildFieldDecls(fields)>) <buildFlattenedStateVectorTuples(s, fields, cfg)>";
}

private str buildFlattenedStateVectorTuples(Spec s, list[Field] fields, Config cfg) {
  str tuples = "";
  
  if (cfg.initialValues[s] != {}) {
    tuples += "\>= {<builFlattenedInitialStateVectorTuples(cfg.initialValues[s], fields)>} ";
  }

  tuples += "\<= {<buildFlattenedStateVectorUpperBound(lookupInstances(s, cfg.instances<0,1>), size(fields), cfg.numberOfTransitions)>}";
  
  return tuples; 
}

private str buildFlattenedStateVectorUpperBound(set[str] instances, int numberOfFlattenedFields, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<primFields>\>" | int c <- [1..numberOfTransitions+1], str i <- instances])
  when str primFields := intercalate(",", ["?" | int i <- [0..numberOfFlattenedFields]]);

private str builFlattenedInitialStateVectorTuples(rel[str instance, str field, set[str] val] initialValues, list[Field] order) 
  = intercalate(",", ["\<c1,<i>,<buildInitialStateVectorFieldValues(initialValues[i], order)>\>" | str i <- initialValues<0>]); 

private str buildInitialStateVectorFieldValues(rel[str field, set[str] val] initialValues, list[Field] order)
  = intercalate(",", ["<v>" | f <- order, result := initialValues["<f.name>"], str v := (result == {} ? "?" : getOneFrom(getOneFrom(result)))]);

private str buildOtherStateVectorRels(Spec spc, Config cfg) {
  list[Field] otherFields = lookupNonPrimFields(spc, cfg.tm);
  
  str rels = "";
  
  for (f <- otherFields) {
    rels += "<getMultStateVectorName(spc,f)> (config:id, instance:id, <toLowerCase("<f.name>")>:id) <buildOtherRelBoundsDecl(spc, f, cfg)>\n";
  }
  
  return rels;
}
private str buildOtherRelBoundsDecl(Spec spc, Field f, Config cfg) {
  str bounds = "";
  
  if (cfg.initialValues[spc] != {}) {
    bounds += "\>= {<buildOtherRelLowerBounds(spc,f,cfg.initialValues[spc])>}";
  }
  
  bounds += "\<= {<buildOtherRelUpperBounds(spc,f,cfg)>}";
  
  return bounds;
}

private str buildOtherRelLowerBounds(Spec spc, Field f, rel[str instance, str field, set[str] val] initialValues)
  = "TODO";
  
private str buildOtherRelUpperBounds(Spec spc, Field f, Config cfg) 
  = intercalate(",", ["\<c<c>,<i>,<t>\>" | int c <- [1..cfg.numberOfTransitions+1], str i <- inst, str t <- instOfType])
  when 
    set[str] inst := lookupInstances(spc, cfg.instances<0,1>),
    list[str] instOfType := getInstancesOfType(f.tipe, cfg.instances<0,1>);
      
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
  