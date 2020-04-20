module rebel::checker::CheckAssembler

import rebel::lang::Syntax;
import rebel::lang::DependencyAnalyzer;
import rebel::lang::TypeChecker;
import rebel::lang::Parser;

import util::PathUtil;

import IO;
import Location;
import ParseTree;
import Set;
import analysis::graphs::Graph;

alias CheckedModule = tuple[Module m, TModel tm];

CheckedModule assembleCheck(str check, loc modLoc, PathConfig pcfg, bool saveGenModule = true) = assembleCheck(check, parseModule(modLoc), pcfg, saveGenModule = saveGenModule);

CheckedModule assembleCheck(str check, Module root, PathConfig pcfg, bool saveGenModule = true) = assembleCheck(check, root, calculateDependencies(root, defaultPathConfig(root@\loc.top)), pcfg, saveGenModule = saveGenModule);

CheckedModule assembleCheck(str check, Module root, Graph[RebelDependency] modDep, PathConfig pcfg, bool saveGenModule = true) {
  if (/resolvedAndCheckedModule(Module m, TModel tm, _) := modDep, /Check chk := m, "<chk.name>" == check) {
    return assembleCheck(chk, root, tm, modDep, pcfg, saveGenModule = saveGenModule);
  } else {
    throw "Check with name `<check>` not found";
  }
}

CheckedModule assembleCheck(Check chk, Module root, TModel tm, Graph[RebelDependency] modDep, PathConfig pcfg, bool saveGenModule = true) {
  if (/resolvedOnlyModule(_,_) := modDep || /unresolvedModule(_) := modDep) {
    throw "Can only assemble check modules when all dependend modules are resolved and type checked";
  } 
  
  set[RebelDependency] deps = {dep | /RebelDependency dep <- modDep}; 
  Config cfg = findReferencedConfig(chk,tm,deps);
  Assert as = findReferencedAssert(chk,tm,deps);

  // Build a spec dependency graph from the module dependency graph
  Graph[Spec] spcDep = extractSpecDependencyGraph(modDep);
  
  bool replace(Type abstractSpcType, Type concreteSpcType) {
    Spec abstractSpc = lookupSpecByRef(tm.useDef[abstractSpcType@\loc], deps);
    Spec concreteSpc = lookupSpecByRef(tm.useDef[concreteSpcType@\loc], deps);
    
    abstractSpc = visit(abstractSpc) {
      case Type t => concreteSpcType when "<t>" == "<abstractSpcType>"
      case Expr e => [Expr]"<concreteSpcType>" when "<e>" == "<abstractSpcType>"
    }; 
    
    abstractSpc.name = concreteSpc.name;
    
    spcDep += {<f,abstractSpc> | <f,t> <- spcDep, t == concreteSpc};
    spcDep = {<f,t> | <Spec f, Spec t> <- spcDep, f != concreteSpc, t != concreteSpc};
      
    return true;
  }  

  cfg = visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type abstractSpc> abstracts <Type concreteSpc> <InState? inState> <WithAssignments? assignments>` =>
      (InstanceSetup)`<{Id ","}+ labels> : <Type concreteSpc> <InState? inState> <WithAssignments? assignments>` when replace(abstractSpc, concreteSpc)
  };  

  set[Spec] filteredSpecs = filterNonReferencedSpecs(spcDep, deps, tm, cfg);  
  Module gen = assembleModule(root.\module.name, filteredSpecs, as, cfg, chk);
  
  if (saveGenModule) {
    writeFile(addModuleToBase(pcfg.checks, gen)[extension="rebel"], gen);
  }
  
  TModel genTm = rebelTModelFromModule(gen, {}, pcfg);
  
  return <gen, genTm>;
}

private set[Spec] filterNonReferencedSpecs(Graph[Spec] spcDep, set[RebelDependency] deps, TModel tm, Config cfg) {
  set[set[Spec]] components = connectedComponents(spcDep);
  set[Spec] referencedSpcs = {lookupSpecByRef(tm.useDef[spc@\loc], deps) | (InstanceSetup)`<{Id ","}+ _> : <Type spc> <InState? _> <WithAssignments? _>` <- cfg.instances};
  
  Spec s = getOneFrom(referencedSpcs);
  for (set[Spec] comp <- components, s in comp) {
    return comp;
  }
  
  throw "Unable to find all referenced specs";
}

private Module assembleModule(QualifiedName origMod, set[Spec] specs, Assert as, Config cfg, Check chk) {
  return [Module]"module <origMod>_<chk.name>
                 '<for (s <- specs) {>
                 '<s>
                 '<}>
                 '
                 '<as>
                 '
                 '<cfg>
                 '
                 '<chk>";
} 

private rebel::lang::Syntax::Config findReferencedConfig(Check chk, TModel tm, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, /rebel::lang::Syntax::Config cfg <- m.parts, {cfg@\loc} == tm.useDef[chk.config@\loc]) {
    return cfg;
  }
  
  throw "Unable to find referenced config at `<chk.config@\loc>`";
}

private rebel::lang::Syntax::Assert findReferencedAssert(Check chk, TModel tm, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, /rebel::lang::Syntax::Assert as <- m.parts, {as@\loc} == tm.useDef[chk.name@\loc]) {
    return as;
  }
  
  throw "Unable to find referenced assert at `<chk.name@\loc>`";
}

private Graph[Spec] extractSpecDependencyGraph(Graph[RebelDependency] modDep) {
  Graph[Spec] spcDepGraph = {}; 

  for (dep1:resolvedAndCheckedModule(Module m, TModel tm, _) <- modDep<0>, /Spec s <- m.parts) {
    // Get all referenced other specs from the current spec 
    for (loc def <- tm.facts, isContainedIn(def, s@\loc), specType(str name) := tm.facts[def]) { 
      spcDepGraph += <s, lookupSpecByName(name, modDep[dep1])>;
    }  
  }

  return spcDepGraph;
}

private Spec lookupSpecByRef({loc specDef}, set[RebelDependency] deps) = lookupSpecByRef(specDef, deps);

private Spec lookupSpecByRef(loc specDef, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, /Spec s <- m.parts, s@\loc == specDef) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specDef>`";
} 

private Spec lookupSpecByName(str name, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, /Spec s <- m.parts) { 
    if ("<s.name>" == name) {
      return s;
    }
  } 
  
  throw "Unable to find spec with name `<name>`"; 
} 

private void printSpcDepGraph(Graph[Spec] spcDepGraph) {
  for (Spec from <- spcDepGraph<0>, Spec to <- spcDepGraph[from]) {
    println("<from.name> -\> <to.name>"); 
  } 
}
