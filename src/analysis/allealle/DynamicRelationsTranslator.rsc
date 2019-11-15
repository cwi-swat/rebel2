module analysis::allealle::DynamicRelationsTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import analysis::allealle::CommonTranslationFunctions;

import String;
import Set;
import List;
import IO;

str translateConfigState(Spec spc, uninitialized()) = "state_uninitialized";
str translateConfigState(Spec spc, finalized())     = "state_finalized";
str translateConfigState(Spec spc, state(str name)) = "state_<toLowerCase("<spc.name>")>_<toLowerCase("<name>")>";

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
  
  for (Spec s <- specs, e <- lookupEvents(s), /FormalParam p <- e.params) {
    rels += buildEventParamRel(s,e,p,cfg);
  }
  
  return intercalate("\n", [r | r <- rels, r != ""]);
}

private str buildEventParamRel(Spec s, Event e, FormalParam p, Config cfg) {
  list[str] defs = ["cur:id", "nxt:id", getParamHeaderDef(p,cfg)];
  return "ParamEvent<getCapitalizedSpecName(s)><getCapitalizedEventName(e)><getCapitalizedParamName(p)> (<intercalate(", ", defs)>) <buildParamTuples(s,e,p,cfg)>";
}  

private str buildParamTuples(Spec s, Event e, FormalParam p, Config cfg) {
  list[str] upperBound = [];  
  for (int i <- [1..cfg.numberOfTransitions]) {
    if (isPrim(p.tipe, cfg.tm)) {
      upperBound += "\<c<i>,c<i+1>,?\>";
    } else {
      for (str otherInst <- getInstancesOfType(p.tipe, cfg.instances<0,1>, cfg.tm)) {
        upperBound += "\<c<i>,c<i+1>,<otherInst>\>";
      }
    } 
  }

  return "\<= {<intercalate(",", upperBound)>}"; 
}

private str buildStateVectors(set[Spec] specs, Config cfg) {
  list[str] rels = [buildFieldRel(s, f, cfg) | Spec s <- specs, /Field f <- s.fields];
  return "<for (r <- rels) {><r>
         '<}>";
}

private str buildFieldRel(Spec spc, Field f, Config cfg) {
  list[str] defs = ["config:id", "instance:id", getFieldHeaderDef(f,cfg)];
  return "<getCapitalizedSpecName(spc)><getCapitalizedFieldName(f)> (<intercalate(", ", defs)>) <buildFieldTuples(spc, f, cfg)>";
}

private str getFieldHeaderDef(Field f, Config cfg) = "<f.name>:<convertType(f.tipe)>"; 
private str getParamHeaderDef(FormalParam p, Config cfg) = "<p.name>:<convertType(p.tipe)>"; 

private str buildFieldTuples(Spec spc, Field f, Config cfg) {
  list[str] lowerBound = [];
  for (<str inst, "<f.name>", str val> <- cfg.initialValues[spc]) {
    lowerBound += "\<c1,<inst>,<val>\>";
  }
  
  list[str] upperBound = [];  
  for (str inst <- lookupInstances(spc, cfg.instances<0,1>), int i <- [(lowerBound == [] ? 1 : 2)..cfg.numberOfTransitions+1]) {
    if (isPrim(f.tipe, cfg.tm)) {
      upperBound += "\<c<i>,<inst>,?\>";
    } else if (isSetOfInt(f.tipe, cfg.tm)) {
      for (int j <- [1..cfg.maxSizeIntegerSets+1]) {
        upperBound += "\<c<i>,<inst>,<inst>_elem<j>\>";
      }
    } else if (isSetOfString(f.tipe, cfg.tm)) {
      for (int j <- [1..cfg.maxSizeStringSets+1]) {
        upperBound += "\<c<i>,<inst>,<inst>_elem<j>\>";
      }
    }else { // Set of other specification
      for (str otherInst <- getInstancesOfType(f.tipe, cfg.instances<0,1>, cfg.tm)) {
        upperBound += "\<c<i>,<inst>,<otherInst>\>";
      }
    } 
  }
  
  if (lowerBound != []) {
    return "\>= {<intercalate(",", lowerBound)>} \<= {<intercalate(",", upperBound)>}";
  } else {
    return "\<= {<intercalate(",", upperBound)>}";
  }
}


private str buildChangedInstancesRel(set[str] instances, int numberOfTransitions) 
  = "changedInstance (cur:id, nxt:id, instance:id) \<= {<intercalate(",", ["\<c<c>,c<c+1>,<i>\>" | int c <- [1..numberOfTransitions], str i <- instances])>}
    '";
  
private str buildRaisedEventsRel(rel[Spec spc, str instance] instances, int numberOfTransitions) 
  = "raisedEvent (cur:id, nxt:id, event:id, instance:id) \<= {<intercalate(",", [tups | <spc, i> <- instances, str tups := buildRaisedEventsTuples(spc, i, numberOfTransitions), tups != ""])>}";

private str buildRaisedEventsTuples(Spec spc, str instance, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,c<c+1>,<toLowerCase(event)>,<instance>\>" | int c <- [1..numberOfTransitions], str event <- lookupRaisableEventName(spc)]);

private str buildConfigRels(int numberOfTransitions)
  = "Config (config:id) \>= {\<c1\>} \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    'order (cur:id, nxt:id) \<= {<intercalate(",", ["\<c<i>,c<i+1>\>" | int i <- [1..numberOfTransitions]])>}
    'first (config:id) = {\<c1\>}
    'last (config:id) \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    'back (config:id) \<= {<intercalate(",", ["\<c<i>\>" | int i <- [1..numberOfTransitions+1]])>}
    'loop (cur:id, nxt:id) \<= {<intercalate(",", ["\<c<i>,c<j>\>" | int i <- [2..numberOfTransitions+1], int j <- [1..i+1]])>}
    '";

private str buildInstanceRel(rel[Spec spc, str instance, State initialState] instances)
  = "Instance (spec:id, instance:id) = {<intercalate(",", ["\<<toLowerCase("<inst.spc.name>")>,<inst.instance>\>" | inst <- instances])>}";
  
private str buildInstanceInStateRel(rel[Spec spc, str instance, State state] instances, int numberOfTransitions) 
  = "instanceInState (config:id, instance:id, state:id) \>= {<buildInitialInstanceInStateTuples(instances)>}\<= {<buildInstanceInStateTuples(instances<spc,instance>, numberOfTransitions)>}";

private str buildInitialInstanceInStateTuples(rel[Spec spc, str instance, State state] instances)
  = intercalate(",", ["\<c1,<i>,<translateConfigState(s, st)>\>" | <s,i,st> <- instances]);

private str buildInstanceInStateTuples(rel[Spec spc, str instance] instances, int numberOfTransitions)
  = intercalate(",", ["\<c<c>,<i>,<toLowerCase(st)>\>" | int c <- [1..numberOfTransitions+1], <s,i> <- instances, str st <- lookupStateLabelsWithDefaultState(s)]);
  