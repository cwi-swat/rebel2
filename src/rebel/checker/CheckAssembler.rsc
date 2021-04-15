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
import DateTime;

import util::Progress;
import util::Benchmark;

alias CheckedModule = tuple[Module m, TModel tm, int duration];

CheckedModule assembleCheck(str check, loc modLoc, PathConfig pcfg, bool saveGenModule = true) = assembleCheck(check, parseModule(modLoc), pcfg, saveGenModule = saveGenModule);

CheckedModule assembleCheck(str check, Module root, PathConfig pcfg, bool saveGenModule = true) = assembleCheck(check, root, calculateDependencies(root, defaultPathConfig(root@\loc.top)), pcfg, saveGenModule = saveGenModule);

CheckedModule assembleCheck(str check, Module root, Graph[RebelDependency] modDep, PathConfig pcfg, bool saveGenModule = true) {
  set[RebelDependency] resAndChecked = {r | r:resolvedAndCheckedModule(_, _, _) <- (modDep<0> + modDep<1>)};  
  
  if (r <- resAndChecked, (Part)`<Check chk>` <- r.m.parts, "<chk.name>" == check) {
    return assembleCheck(chk, root, r.tm, modDep, pcfg, saveGenModule = saveGenModule);
  } else {
    throw "Check with name `<check>` not found";
  }
}

CheckedModule assembleCheck(Check chk, Module root, TModel tm, Graph[RebelDependency] modDep, PathConfig pcfg, bool saveGenModule = true) {
  print("Preparing module for check ...");
  int startTime = cpuTime();
    
  //if (/resolvedOnlyModule(_,_) := modDep || /unresolvedModule(_) := modDep) {
  //  throw "Can only assemble check modules when all dependend modules are resolved and type checked";
  //} 
  //println("After checking if all modules are resolved: <(cpuTime() - startTime) / 1000000>ms");
  
  set[RebelDependency] deps = {d1,d2 | <RebelDependency d1, RebelDependency d2> <- modDep}; 
  Config cfg = findReferencedConfig(chk,tm,deps);
  Assert as = findReferencedAssert(chk,tm,deps);
  if ((Command)`check` := chk.cmd) { // Command is check, start finding counterexample by negating the assertion
    as = parse(#Assert, "assert <as.name> = !(<as.form>);");
  }
  //println("After gathering dependencies: <(cpuTime() - startTime) / 1000000>ms");
  
  // Build a spec dependency graph from the module dependency graph
  Graph[Spec] spcDep = extractSpecDependencyGraph(modDep);
  //println("After extracting spec dependency grap: <(cpuTime() - startTime) / 1000000>ms");
  
  // Merge all useDef relations 
  rel[loc,loc] globDefUse = {*dep1.tm.useDef<1,0>,*dep2.tm.useDef<1,0> | <RebelDependency dep1, RebelDependency dep2> <- modDep};
  //println("After merging all defUses: <(cpuTime() - startTime) / 1000000>ms");
    
  bool replace(Type abstractSpcType, Type concreteSpcType) {
    Spec abstractSpc = lookupSpecByRef(tm.useDef[abstractSpcType@\loc], deps);
    Spec concreteSpc = lookupSpecByRef(tm.useDef[concreteSpcType@\loc], deps);
    
    Spec unalteredAbstractSpc = abstractSpc;
    
    abstractSpc = visit(abstractSpc) {
      case Type t => concreteSpcType when "<t>" == "<abstractSpcType>"
      case Expr e => [Expr]"<concreteSpcType>" when "<e>" == "<abstractSpcType>"
    }; 
    
    abstractSpc.name = concreteSpc.name;
    
    spcDep += {<f,abstractSpc> | <f,t> <- spcDep, t == concreteSpc};
    spcDep = {<f,t> | <Spec f, Spec t> <- spcDep, f != concreteSpc, t != concreteSpc};
    
    // remove the original mock spec from the depencendies
    spcDep -= {<unalteredAbstractSpc,unalteredAbstractSpc>};
      
    return true;
  }  

  bool slice(set[Id] fields) {
    set[Spec] allSpecs = {s | Spec s <- spcDep<0>+spcDep<1>};
    
    for (Id field <- fields) {
      Field fld = lookupFieldByRef(tm.useDef[field@\loc], spcDep);
      
      // Find all the uses of the field
      set[loc] uses = globDefUse[fld.name@\loc]; 

      // Remove all fields, formula's in pre and post and facts that reference the 'forgotten' field
      allSpecs = visit(allSpecs) {
        case Spec s => filterFieldAndFacts(fld, s, uses)
        case Pre pre => filterPre(pre, uses)    
        case Post post => filterPost(post, uses)
      }
      
      // Remove all parameters that became unused
      allSpecs = visit(allSpecs) {
        case Event e => filterParameters(e, globDefUse)
      } 
    }
    
    // Replace all occurrences of the specs in the spec dependency graph      
    spcDep = visit(spcDep) {
      case Spec orig => changed when Spec changed <- allSpecs, changed@\loc == orig@\loc
    }

    return true;
  }

  // Step 1: Apply abstraction
  cfg = visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type abstractSpc> mocks <Type concreteSpc> <Forget? forget> <InState? inState> <WithAssignments? assignments>` =>
      (InstanceSetup)`<{Id ","}+ labels> : <Type concreteSpc> <Forget? forget> <InState? inState> <WithAssignments? assignments>` when replace(abstractSpc, concreteSpc)
  };  
  //println("After applying abstractions: <(cpuTime() - startTime) / 1000000>ms");
  
  // Step 2: Apply slicing (removing 'forgotten' fields)
  cfg = visit (cfg) {
    case (InstanceSetup)`<{Id ","}+ labels> : <Type spc> forget <{Id ","}+ fields> <InState? inState> <WithAssignments? assignments>` =>
      (InstanceSetup)`<{Id ","}+ labels> : <Type spc> <InState? inState> <WithAssignments? assignments>` when slice({f | f <- fields})
  };  
  //println("After applying slicing: <(cpuTime() - startTime) / 1000000>ms");

  set[Spec] filteredSpecs = filterNonReferencedSpecs(spcDep, tm, cfg);  
  //println("After filtering non referenced specs: <(cpuTime() - startTime) / 1000000>ms");

  Module gen = assembleModule(root.\module.name, filteredSpecs, as, cfg, chk);
  //println("After assembling new module: <(cpuTime() - startTime) / 1000000>ms");
  TModel genTm = rebelTModelFromModule(gen, {}, pcfg);
  //println("After type checking new module: <(cpuTime() - startTime) / 1000000>ms");
  
  Module genMod = gen;
  
  // Filter the specs until none can be removed any more
  Graph[Spec] newSpcDep = extractSpecDependencyGraph({<resolvedAndCheckedModule(gen,genTm,now()), resolvedAndCheckedModule(gen,genTm,now())>});
  if (size(newSpcDep) != size(spcDep)) {
    filteredSpecs = filterNonReferencedSpecs(newSpcDep, genTm, findConfig(gen));  
    gen = assembleModule(root.\module.name, filteredSpecs, as, cfg, chk);
    
    // TEMP / TODO: Cop-out for Type checking issues with generated code (without reparsing). Location trouble on generated nodes
    genMod = parse(#Module, "<gen>");
    ////////////////
    
    genTm = rebelTModelFromModule(genMod, {}, pcfg);
  }
  //println("After filtering one last time: <(cpuTime() - startTime) / 1000000>ms");
    
  if (saveGenModule) {
    writeFile(addModuleToBase(pcfg.checks, gen)[extension="rebel"], gen);
  }

  int duration = (cpuTime() - startTime) / 1000000;

  println("done, took: <duration> ms.");
  
  return <genMod, genTm, duration>;
}

private Spec filterFieldAndFacts(Field fld, Spec s, set[loc] uses) = filterFacts(filterField(s, fld), uses);

private Spec filterField(spc:(Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Pred* preds> <Fact* fcts> <States? sts>`, Field fld) {
  if (size({f | /Field f := flds}) == 1, /fld := flds) {
    return ((Spec)`spec <Id name> <Instances? inst> <Constraints? cons> <Event* evnts> <Fact* fcts> <States? sts>`)[@\loc=spc@\loc];
  }
  
  Fields filterFields((Fields)`<Field f>, <{Field ","}+ after>;`)
    = (Fields)`<{Field ","}+ after>;` when f == fld; 

  Fields filterFields((Fields)`<{Field ","}+ before>, <Field f>;`)
    = (Fields)`<{Field ","}+ before>;` when f == fld; 

  Fields filterFields((Fields)`<{Field ","}+ before>, <Field f>, <{Field ","}+ after>;`)
    = (Fields)`<{Field ","}+ before>, <{Field ","}+ after>;` when f == fld; 

  return visit(spc) {
    case Fields ff => filterFields(ff) when /fld := ff 
  }
}

private Event filterParameters(Event evnt, rel[loc,loc] defUse) {
  Event filterParam((Event)`<Modifier* modifiers> event <Id name>(<FormalParam p>) <EventBody body>`, FormalParam pp) 
    = (Event)`<Modifier* modifiers> event <Id name>() <EventBody body>` when p == pp;
    
  Event filterParam((Event)`<Modifier* modifiers> event <Id name>(<FormalParam p>,<{FormalParam ","}* after>) <EventBody body>`, FormalParam pp) 
    = (Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* after>) <EventBody body>` when p == pp;

  Event filterParam((Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* before>,<FormalParam p>) <EventBody body>`, FormalParam pp) 
    = (Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* before>) <EventBody body>` when p == pp;

  Event filterParam((Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* before>,<FormalParam p>,<{FormalParam ","}* after>) <EventBody body>`, FormalParam pp) 
    = (Event)`<Modifier* modifiers> event <Id name>(<{FormalParam ","}* before>,<{FormalParam ","}* after>) <EventBody body>` when p == pp;

  bool isUsed(FormalParam p) {
    for (loc use <- defUse[p.name@\loc]) {
      visit (evnt) {
        case Pre pre: {
          if (Formula f <- pre.formulas, isContainedIn(use, f@\loc)) {
            return true;
          }
        }
        case Post post: {
          if (Formula f <- post.formulas, isContainedIn(use, f@\loc)) {
            return true;
          }
        }
      } 
    }
    
    return false;
  }
  
  for (FormalParam p <- evnt.params, !isUsed(p)) {
    evnt = filterParam(evnt, p);
  }
      
  return evnt;
}

private Pre filterPre(Pre pre, set[loc] uses) {
  Pre filterPre(p:(Pre)`pre: <Formula ff>;`, Formula f)
    = (Pre)`pre: ;`[@\loc=p@\loc] when ff == f;

  Pre filterPre(p:(Pre)`pre: <{Formula ","}* form>, <Formula ff>;`, Formula f)
    = (Pre)`pre: <{Formula ","}* form>;`[@\loc=p@\loc] when ff == f;

  Pre filterPre(p:(Pre)`pre: <Formula ff>, <{Formula ","}* form>;`, Formula f)
    = (Pre)`pre: <{Formula ","}* form>;`[@\loc=p@\loc] when ff == f;

  Pre filterPre(p:(Pre)`pre: <{Formula ","}* before>, <Formula ff>, <{Formula ","}* after>;`, Formula f)
    = (Pre)`pre: <{Formula ","}* before>, 
           '     <{Formula ","}* after>;`[@\loc=p@\loc] when ff == f;
      
  for (loc use <- uses, isContainedIn(use, pre@\loc), Formula f <- pre.formulas, isContainedIn(use, f@\loc)) {
    pre = filterPre(pre, f); 
  }
  
  return pre;
}

private Post filterPost(Post post, set[loc] uses) {
  Post filterPost(p:(Post)`post: <Formula ff>;`, Formula f)
    = (Post)`post: ;`[@\loc=p@\loc] when ff == f;

  Post filterPost(p:(Post)`post: <{Formula ","}* form>, <Formula ff>;`, Formula f)
    = (Post)`post: <{Formula ","}* form>;`[@\loc=p@\loc] when ff == f;

  Post filterPost(p:(Post)`post: <Formula ff>, <{Formula ","}* form>;`, Formula f)
    = (Post)`post: <{Formula ","}* form>;`[@\loc=p@\loc] when ff == f;

  Post filterPost(p:(Post)`post: <{Formula ","}* before>, <Formula ff>, <{Formula ","}* after>;`, Formula f)
    = (Post)`post: <{Formula ","}* before>, 
            '      <{Formula ","}* after>;`[@\loc=p@\loc] when ff == f;
      
  for (loc use <- uses, isContainedIn(use, post@\loc), Formula f <- post.formulas, isContainedIn(use, f@\loc)) {
    post = filterPost(post, f); 
  }
  
  return post;
}

private Spec filterFacts(Spec spc, set[loc] uses) {
  Spec filterFact(s:(Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact ff> <States? sts>`, Fact f)
    = (Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <States? sts>`[@\loc=s@\loc] when ff == f;

  Spec filterFact(s:(Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact ff> <Fact* other> <States? sts>`, Fact f)
    = (Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact* other> <States? sts>`[@\loc=s@\loc] when ff == f;

  Spec filterFact(s:(Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact* other> <Fact ff> <States? sts>`, Fact f)
    = (Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact* other> <States? sts>`[@\loc=s@\loc] when ff == f;

  Spec filterFact(s:(Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact* before> <Fact ff> <Fact* after> <States? sts>`, Fact f)
    = (Spec)`spec <Id name> <Instances? inst> <Fields? flds> <Constraints? cons> <Event* evnts> <Fact* before> <Fact* after> <States? sts>`[@\loc=s@\loc] when ff == f;

  for (loc use <- uses, Fact f <- spc.facts, isContainedIn(use, f@\loc)) {
    spc = filterFact(spc, f);
  }
   
  return spc;
}

private set[Spec] filterNonReferencedSpecs(Graph[Spec] spcDep, TModel tm, Config cfg) {
  set[Spec] referencedSpcs = {lookupSpecByName("<spc>", spcDep) | (InstanceSetup)`<{Id ","}+ _> : <Type spc> <InState? _> <WithAssignments? _>` <- cfg.instances};
  set[Spec] reachable = reach(spcDep, referencedSpcs);
  
  set[Spec] filtered = referencedSpcs + reachable;

  if (filtered == {}) {  
    throw "Unable to find all referenced specs";
  }
  
  return filtered;
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

private rebel::lang::Syntax::Config findConfig(Module m) = c when /rebel::lang::Syntax::Config c := m.parts;

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

  for (dep1:resolvedAndCheckedModule(Module m, TModel tm, _) <- modDep<0>, (Part)`<Spec s>` <- m.parts) {
    // Always add self-dependency
    spcDepGraph += <s,s>;
    // Get all referenced other specs from the current spec 
    for (loc def <- tm.facts, isContainedIn(def, s@\loc), specType(str name) := tm.facts[def]) { 
      spcDepGraph += <s, lookupSpecByName(name, modDep[dep1])>;
    }  
  }

  return spcDepGraph;
}

private Field lookupFieldByRef({loc fldDef}, Graph[Spec] spcDeps) = lookupFieldByRef(fldDef, spcDeps);
private Field lookupFieldByRef(loc fldDef, Graph[Spec] spcDeps) {
  for (Spec s <- spcDeps<0>+spcDeps<1>, /Field f := s.fields, f.name@\loc == fldDef) {
    return f;
  } 
  
  throw "Unable to find referenced Field at `<fldDef>`";
} 

private Spec lookupSpecByRef({}, Graph[Spec] spcDeps) { throw "No definition found for ref"; }
private Spec lookupSpecByRef({loc specDef}, Graph[Spec] spcDeps) = lookupSpecByRef(specDef, spcDeps);
private Spec lookupSpecByRef(loc specDef, Graph[Spec] spcDeps) {
  for (Spec s <- spcDeps<0>+spcDeps<1>, s@\loc == specDef) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specDef>`";
}

private Spec lookupSpecByRef({}, set[RebelDependency] deps) { throw "No definition found for ref"; }
private Spec lookupSpecByRef({loc specDef}, set[RebelDependency] deps) = lookupSpecByRef(specDef, deps);
private Spec lookupSpecByRef(loc specDef, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, (Part)`<Spec s>` <- m.parts, s@\loc == specDef) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specDef>`";
} 

private Spec lookupSpecByName(str name, set[RebelDependency] deps) {
  for (resolvedAndCheckedModule(Module m, _, _) <- deps, (Part)`<Spec s>` <- m.parts) { 
    if ("<s.name>" == name) {
      return s;
    }
  } 
  
  throw "Unable to find spec with name `<name>`"; 
} 

private Spec lookupSpecByName(str name, Graph[Spec] spcDeps) {
  for (Spec s <- spcDeps<0>+spcDeps<1>) { 
    if ("<s.name>" == name) {
      return s;
    }
  }
  
  throw "Unable to find referenced Spec at `<specDef>`";
}

private void printSpcDepGraph(Graph[Spec] spcDepGraph) {
  for (Spec from <- spcDepGraph<0>, Spec to <- spcDepGraph[from]) {
    println("<from.name> -\> <to.name>"); 
  } 
}
