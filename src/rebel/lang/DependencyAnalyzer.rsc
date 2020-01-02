module rebel::lang::DependencyAnalyzer

import rebel::lang::Syntax;
import rebel::lang::Parser;
//import rebel::lang::TypeChecker;

import util::PathUtil;
import util::Maybe;

extend analysis::graphs::Graph;
import analysis::typepal::Collector;

import IO; 
import ValueIO; 
import String;
import DateTime;
import Set;
import List;

data RebelDependency
  = resolvedAndCheckedModule(Module m, TModel tm, datetime timestamp)
  | resolvedOnlyModule(Module m, datetime timestamp)
  | unresolvedModule(QualifiedName fqn)
  ;

Graph[RebelDependency] calculateDependencies(Module m, PathConfig pcfg) {
  map[QualifiedName,RebelDependency] done = ();
  Maybe[RebelDependency] isDone(QualifiedName n) = just(done[n]) when n in done;
  Maybe[RebelDependency] isDone(QualifiedName n) = nothing() when n notin done;
  void addToDone(RebelDependency dep) { done[dep.m.\module.name] = dep; }
  
  Graph[RebelDependency] deps = calculateDependencies(buildDependency(m, pcfg), pcfg, isDone, addToDone);
  
  println("Resolved dependencies: <intercalate(", ", [d.m.\module.name | d <- (deps<0> + deps<1>), d has m])>");
  println("Unresolved dependencies: <intercalate(", ", ["<fqn>" | unresolvedModule(QualifiedName fqn) <- (deps<0> + deps<1>)])>");
  
  return deps;
}

RebelDependency buildDependency(Module m, PathConfig pcfg) 
  = (just(loc tmLoc) := lookupTModel(m.\module.name, pcfg))
  ? resolvedAndCheckedModule(m, readBinaryValueFile(#TModel, tmLoc), lastModified(tmLoc)) 
  : resolvedOnlyModule(m, lastModified(m@\loc.top))
  ;  
  
private Graph[RebelDependency] calculateDependencies(RebelDependency cur, PathConfig pcfg, Maybe[RebelDependency] (QualifiedName) done, void (RebelDependency) addToDone) {
  addToDone(cur);
  
  Graph[RebelDependency] sub = {};
  // add self-dependency   
  sub += <cur,cur>;
    
  for (Import imp <- cur.m.imports) {
    if (just(RebelDependency other) := done(imp.\module)) {
      sub += <cur, other>;    
    } 
    else if (just(loc impLoc) := lookupModule(imp.\module, pcfg)) {
      Module n = parseModule(impLoc);
      
      RebelDependency other = buildDependency(n, pcfg);

      sub += calculateDependencies(other, pcfg, done, addToDone);
      sub += <cur, other>;
    } 
    else {
      sub += <cur, unresolvedModule(imp.\module)>;
    }   
  }
  
  return sub;
}

set[Module] findDirtyModules(Module root, Graph[RebelDependency] depGraph) {
  set[Module] dirty = {root};
  
  list[RebelDependency] todo = [d | d <- order(depGraph), unresolvedModule(QualifiedName fqn) !:= d];
    
  void checkParents(RebelDependency dep, datetime newest) {
    if (dep notin todo) {
      return; // already checked it
    }
    
    todo -= dep;
    
    if ((resolvedAndCheckedModule(Module m, TModel tm, datetime timestamp) := dep && timestamp < newest) ||
        (resolvedOnlyModule(Module m, datetime timestamp) := dep)) {
      dirty += m;
      newest = now();
    }
    
    for (set[RebelDependency] parents := predecessors(depGraph, dep), parent <- parents) {
      checkParents(parent, newest);
    }
  }
  
  while (todo != []) {
    println("Todo: <["<m.m.\module.name>" | m <- todo]>");
    
    RebelDependency current = todo[-1];
    println("Checking module: <current.m.\module.name>, timestamp = <current.timestamp>");
    checkParents(current, current.timestamp);
  }  
  
  println("Found dirty modules from <root.\module.name>: <intercalate(", ", ["<m.\module.name>" | m <- dirty])>");  
  return dirty;   
}

Maybe[TModel] getTModel(Module m, Graph[RebelDependency] depGraph) {
  if (/resolvedAndCheckedModule(Module mm, TModel tm, _) := depGraph<0> + depGraph<1>, mm@\loc.top == m@\loc.top) {
    return just(tm);
  }
  
  return nothing();
}


private Maybe[loc] lookupModule(QualifiedName name, PathConfig pcfg) = lookupFile(name, "rebel", pcfg.srcs);
private Maybe[loc] lookupTModel(QualifiedName name, PathConfig pcfg) = lookupFile(name, "tm", pcfg.tmodels);


