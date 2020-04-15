module rebel::checker::translation::ConfigTranslator

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;
import rebel::checker::translation::RelationCollector;
import rebel::checker::translation::CommonTranslationFunctions;

import String;
import IO;
import Set;
import List;

Config buildConfig(str checkName, set[Module] mods, TModel tm) {
  if (Module m <- mods, 
    /chk:(Check)`check <Id name> from <Id cfg> in <SearchDepth depth> <Objectives? _>;` <- m.parts, "<name>" == checkName) {
    rebel::lang::Syntax::Config c = findReferencedConfig(cfg@\loc, mods, tm);
     
    rel[Spec,str,State] instances = buildInstances(c, mods, tm);
    rel[Spec,str,str,str] initialValues = buildInitialValues(c, mods, tm);
    int searchDepth = buildSearchDepth(depth);  
    bool infiniteTrace = withInfiniteTrace(chk);
    
    set[Fact] facts = gatherFacts(mods);
    
    return config(instances, initialValues, facts, tm, searchDepth, finiteTrace = !infiniteTrace);
   }
   
   throw "Unable to find check with name `<checkName>`";
}

str config2Str(Config cfg) 
  = "<for (Spec s <- cfg.instances<0>) {><s.name>: <intercalate(", ", ["<inst>(<config2Str(s,inst,cfg)>)" | str inst <- cfg.instances[s]<0>])>
    '<}>";

str config2Str(Spec s, str instance, Config cfg) 
  = intercalate(", ", ["<fieldName> = <val>" | <str fieldName, str val> <- cfg.initialValues[s,instance]]);

int buildSearchDepth((SearchDepth)`max <Int steps> steps`) = toInt("<steps>") + 1;

bool withInfiniteTrace(Check chk) = /(Objective)`infinite trace` := chk;

rebel::lang::Syntax::Config findReferencedConfig(loc ref, set[Module] mods, TModel tm) {
  for (Module m <- mods, /rebel::lang::Syntax::Config cfg <- m.parts, {cfg@\loc} == tm.useDef[ref]) {
    return cfg;
  }
  
  throw "Unable to find definition of Config referenced at `<ref>`";
}

set[Fact] gatherFacts(set[Module] mods) = {f | Module m <- mods, /Fact f <- m.parts}; 

rel[Spec spc, str instance, State initialState] buildInstances(rebel::lang::Syntax::Config cfg, set[Module] mods, TModel tm) {
//rel[Spec spc, str instance, State initialState] buildInstances(rebel::lang::Syntax::Config cfg, set[Spec] specs) {
  rel[Spec,str,State] instances = {};

  visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type spec> <InState? inState> <WithAssignments? assignments>` : {
      Spec s = lookupSpecByRef(spec@\loc, mods, tm);
      
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
  instances += {<s,"<instance>",noState()> | Module m <- mods, /Spec s <- m.parts, /Id instance <- s.instances};

  return instances;
} 

rel[Spec spc, str instance, str field, str val] buildInitialValues(rebel::lang::Syntax::Config cfg, set[Module] mods, TModel tm) {
  rel[Spec,str,str,str] initialValues = {};
  
  visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type spec> <Abstracts? _> <InState? _> <WithAssignments assignments>` : {
      Spec s = lookupSpecByRef(spec@\loc, mods, tm);
      initialValues += {<s, "<label>", field, v> | <str field, str v> <- buildAssignments(assignments), Id label <- labels};           
    }
    case (InstanceSetup)`<Id label> <WithAssignments assignments>` : {
      Spec s = lookupSpecByType(tm.facts[label@\loc], mods, tm);
      initialValues += {<s, "<label>", field, v> | <str field, str v> <- buildAssignments(assignments)};           
    }    
  }

  return initialValues;
}

rel[str field, str val] buildAssignments(WithAssignments assignments) {
  set[str] translateLit((Expr)`<Id id>`) = {"<id>"};
  set[str] translateLit((Expr)`<Int i>`) = {"<i>"};
  set[str] translateLit((Expr)`<StringConstant s>`) = {"<s>"};
  set[str] translateLit((Expr)`{<{Expr ","}* elems>}`) = {"<e>" | e <- elems};  
  set[str] translateLit((Expr)`<Expr spc>[<Id inst>]`) = {"<inst>"};
  default set[str] translateLit(Lit l) { throw "No translation function for literal `<l>`";};
  
  rel[str,str] vals = {};
  
  for ((Assignment)`<Id fieldName> = <Expr val>` <- assignments.assignments, str v <- translateLit(val)) {
    vals += <"<fieldName>", v>;
  }
    
  return vals;
}

Spec lookupSpecByType(specType(str name), set[Spec] specs) {
  for (Spec s <- specs, "<s.name>" == name) {
    return s;
  }  

  throw "Unable to find referenced Spec with name `<name>`";
}

Spec lookupSpecByRef(loc specRef, set[Module] mods, TModel tm) {
  for (Module m <- mods, /Spec s <- m.parts, {s@\loc} == tm.useDef[specRef]) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specRef>`";
} 

Spec lookupSpecByRef(loc specRef, set[Module] mods, TModel tm) {
  for (Module m <- mods, /Spec s <- m.parts, {s@\loc} == tm.useDef[specRef]) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specRef>`";
} 

