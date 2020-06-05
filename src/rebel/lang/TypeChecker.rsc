module rebel::lang::TypeChecker

extend rebel::lang::CommonTypeChecker;
extend rebel::lang::SpecTypeChecker;
extend rebel::lang::CheckTypeChecker; 

import rebel::lang::DependencyAnalyzer;
import rebel::lang::Syntax;
import rebel::lang::WellFormednessChecker;

import util::PathUtil;
 
extend analysis::typepal::TypePal;

import IO;
import ValueIO;
import String;

import DateTime;

alias TypeCheckerResult = tuple[TModel tm, Graph[RebelDependency] depGraph];

TypeCheckerResult checkModule(Module root, Graph[RebelDependency] depGraph, PathConfig pcfg, bool saveTModels = true, bool refreshRoot = false, bool debug = false) {
  // If the models should not be saved, just create the (transitive) tmodel
  if (!saveTModels) {
    return <rebelTModelFromModule(root, depGraph, pcfg, saveTModels = false, debug = debug), depGraph>;   
  }
  
  list[RebelDependency] todo = [d | d <- order(depGraph), unresolvedModule(QualifiedName fqn) !:= d];
   
  bool shouldRefresh(datetime timestamp, datetime newest, Module m) 
    = (m == root) 
    ? (refreshRoot || (timestamp < newest)) 
    : (timestamp < newest)
    ;
    
  void check(RebelDependency dep, datetime newest) {
    if (dep notin todo) {
      return; // already checked it
    }

    todo -= dep;
    
    if ((resolvedAndCheckedModule(Module m, TModel tm, datetime timestamp) := dep && shouldRefresh(timestamp, newest, m)) ||
        resolvedOnlyModule(Module m, datetime timestamp) := dep) {
      // need to check the dependency
      newest = now();
      TModel newTM = rebelTModelFromModule(m, subgraph(dep,depGraph), pcfg, saveTModels = saveTModels, debug = debug);
      
      depGraph = visit(depGraph) {
        case RebelDependency d => resolvedAndCheckedModule(m, newTM, newest) when d == dep
      }      
    }
    
    for (set[RebelDependency] parents := predecessors(depGraph, dep), parent <- parents) {
      check(parent, newest);
    }
  }
    
  while (todo != []) {
    RebelDependency current = todo[-1];
    check(current, lastModified(current.m@\loc.top));
  }  
  
  if (/resolvedAndCheckedModule(Module m, TModel tm, datetime _) := depGraph, m == root) {
    return <tm, depGraph>;
  } else {
    throw "Unable to find resolved root module `<root.\module.name>` in type checked dependency graph";
  }   
}

private Graph[RebelDependency] subgraph(RebelDependency from, Graph[RebelDependency] depGraph) = {<from,d> | <from, RebelDependency d> <- depGraph};

private AType rebelBuiltInTypes(AType containerType, Tree selector, loc _, Solver s) {
    if(!(containerType == stringType() && "<selector>" == "length")){
        s.report(error(selector, "Undefined field %q on %t", "<selector>", containerType));
    }
    
    return intType();
}

TModel rebelTModelFromModule(Module root, Graph[RebelDependency] depGraph, PathConfig pcfg, bool saveTModels = false, bool debug = false){
  c = newCollector("collectAndSolve", root, config = tconfig(getTypeNamesAndRole = rebelTypeNamesAndRole,
                                                             getTypeInNamelessType = rebelBuiltInTypes,
                                                             isSubType = subtype,
                                                             verbose=debug, 
                                                             logTModel = debug, 
                                                             logAttempts = debug, 
                                                             logSolverIterations= debug, 
                                                             logSolverSteps = debug));  

  collect(root, c);

  for (RebelDependency dep <- depGraph<0> + depGraph<1>, dep has m, dep.m != root) {
    switch (dep) {
      case resolvedAndCheckedModule(Module m, TModel tm, datetime ts): { println("Importing TModel for `<m.\module.name>`"); c.addTModel(tm); } 
      case resolvedOnlyModule(Module m, datetime ts): collect(m, c);
    }
  }

  
  TModel model = newSolver(root, c.run()).run();
  model = checkWellFormedness(root, model); 
  
  if (saveTModels) { 
    println("Saving new TModel for `<root.\module.name>`");
    saveModule(root,model,pcfg);
  }
  
  return model;
}


private void saveModule(Module m, TModel model, PathConfig pcfg) {
  loc tmFile = (pcfg.tmodels + replaceAll("<m.\module.name>", "::", "/"))[extension = "tm"];
  
  //println("TM file is <tmFile>");
  // filter tmodel  
  makeDirRecursively(tmFile.parent);
  //println("Dirs made");
  writeBinaryValueFile(tmFile, filterTModel(model));
  //println("TM saved");  
}

private TModel filterTModel(TModel tm) {
    println("Filtering TModel before saving");
    tm.config = tconfig();
    
    tm.defines = {d | Define d <- tm.defines, defTypeCall(_,_) !:= d.defInfo};
    tm.definitions = ( d.defined : d | Define d <- tm.defines);
    tm.calculators = {};
    
    //if(tm.config.logImports) println("defines: <size(tm.defines)> ==\> <size(defs)>");
    //m1.defines = toSet(defs);
    //m1 = visit(m1) {case loc l : if(!isEmpty(l.fragment)) insert l[fragment=""]; };
    //m1.definitions = ( def.defined : def | Define def <- m1.defines);
    
    return tm;
}

