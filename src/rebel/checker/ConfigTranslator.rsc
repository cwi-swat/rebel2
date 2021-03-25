module rebel::checker::ConfigTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

//import rebel::checker::translation::RelationCollector;
import rebel::checker::translation::CommonTranslationFunctions;

import String;
import Set;
import List;

import util::Benchmark;

data Config = config(rel[Spec spc, str instance, State initialState] instances, 
                     rel[Spec spc, str instance, str field, str val] initialValues, 
                     int numberOfTransitions,
                     bool finiteTrace = true,
                     bool exactNrOfSteps = false,
                     int maxSizeIntegerSets = 5,
                     int maxSizeStringSets = 5);

alias ConfigBuilderResult = tuple[Config cfg, int duration];
 
ConfigBuilderResult buildConfig(rebel::lang::Syntax::Config cfg, Module m, TModel tm, int searchDepth, bool exactNrOfSteps, bool infiniteTrace) {
  int startTime = cpuTime();
  
  rel[Spec,str,State] instances = buildInstances(cfg, m, tm);
  rel[Spec,str,str,str] initialValues = buildInitialValues(cfg, m, tm);
  int duration = (cpuTime() - startTime) / 1000000;
  
  return <config(instances, initialValues, searchDepth, exactNrOfSteps = exactNrOfSteps, finiteTrace = !infiniteTrace), duration>;
}

str config2Str(Config cfg) 
  = "<for (Spec s <- cfg.instances<0>) {><s.name>: <intercalate(", ", ["<inst>(<config2Str(s,inst,cfg)>)" | str inst <- cfg.instances[s]<0>])>
    '<}>";

str config2Str(Spec s, str instance, Config cfg) 
  = intercalate(", ", ["<fieldName> = <val>" | <str fieldName, str val> <- cfg.initialValues[s,instance]]);

rel[Spec spc, str instance, State initialState] buildInstances(rebel::lang::Syntax::Config cfg, Module m, TModel tm) {
  rel[Spec,str,State] instances = {};

  visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type spec> <InState? inState> <WithAssignments? assignments>` : {
      Spec s = lookupSpecByRef(spec@\loc, m, tm);
      
      State st = noState();
      if (/InState ist := inState) {
        if ("<ist.state>" == "uninitialized") {
          st = uninitialized();
        } else {
          st = state("<ist.state>");
        }
      }
      
      instances += {<s, "<label>", st> | Id label <- labels};
    }    
  }
  
  // Add the 'enumeration instances'
  instances += {<s,"<instance>",noState()> | /Spec s <- m.parts, /Id instance <- s.instances};

  return instances;
} 

rel[Spec spc, str instance, str field, str val] buildInitialValues(rebel::lang::Syntax::Config cfg, Module m, TModel tm) {
  rel[Spec,str,str,str] initialValues = {};
  
  visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type spec> <Mocks? _> <InState? _> <WithAssignments assignments>` : {
      Spec s = lookupSpecByRef(spec@\loc, m, tm);
      initialValues += {<s, "<label>", field, v> | <str field, str v> <- buildAssignments(assignments), Id label <- labels};           
    }
    case (InstanceSetup)`<Id label> <WithAssignments assignments>` : {
      Spec s = lookupSpecByType(tm.facts[label@\loc], m);
      initialValues += {<s, "<label>", field, v> | <str field, str v> <- buildAssignments(assignments)};           
    }    
  }

  return initialValues;
}

rel[str field, str val] buildAssignments(WithAssignments assignments) {  
  set[str] translateLit((Expr)`<Id id>`) = {"<id>"};
  set[str] translateLit((Expr)`<Int i>`) = {"<i>"};
  set[str] translateLit((Expr)`-<Int i>`) = {"-<i>"};
  set[str] translateLit((Expr)`<StringConstant s>`) = {"<s>"};
  set[str] translateLit((Expr)`{<{Expr ","}* elems>}`) = els when els := {"<e>" | e <- elems}, els != {};  
  default set[str] translateLit((Expr)`{<{Expr ","}* elems>}`) = {"__none"};
  set[str] translateLit((Expr)`<Expr spc>[<Id inst>]`) = {"<inst>"};
  set[str] translateLit((Expr)`none`) = {"__none"};
  default set[str] translateLit(Lit l) { throw "No translation function for literal `<l>`";};
  
  rel[str,str] vals = {};
  
  for ((Assignment)`<Id fieldName> = <Expr val>` <- assignments.assignments, str v <- translateLit(val)) {
    vals += <"<fieldName>", v>;
  }
    
  return vals;
}

Spec lookupSpecByType(specType(str name), Module m) {
  for (/Spec s <- m.parts, "<s.name>" == name) {
    return s;
  }  

  throw "Unable to find referenced Spec with name `<name>`";
}

Spec lookupSpecByRef(loc specRef, Module m, TModel tm) {
  for (/Spec s <- m.parts, {s@\loc} == tm.useDef[specRef]) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specRef>`";
} 