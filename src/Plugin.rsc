module Plugin

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::Normalizer;
import rebel::checker::Rebel2Alle;
import rebel::checker::RebelTrace;
 
import util::IDE;
import util::HtmlDisplay;
import util::Prompt; 
import util::Maybe;  

import salix::App;
import rebel::vis::ModuleVis;
import rebel::vis::TraceVis;

import ParseTree;
import Location;
import util::PathUtil; 

import IO; 

void main() {
  str REBEL2_LANGUAGE = "Rebel2 Language";
  registerLanguage(REBEL2_LANGUAGE,"rebel", parseModule);
  
  registerContributions(REBEL2_LANGUAGE, getRebelContributions());
}

alias VisConfig = tuple[int port, tuple[void () serve, void () stop] app];

set[Contribution] getRebelContributions() {

  Content runCheck(Module m, loc selection) {
    if (/Check chk <- m.parts, isContainedIn(selection, chk@\loc)) {
      println("Running check");
      Trace t = performCheck("<chk.name>", m, defaultPathConfig(m@\loc.top), normalizerPathConfig(m@\loc.top));
      
      switch(t) {
        case noTrace(solverTimeout()): {
          alert("Solver timed out. Please simplify the check");
          throw "Solver timed out";
        }
        case noTrace(noSolutionFound()): {
          alert("No trace found. Check not satisfiable for the given configuration");
          throw "No trace found";
        }
        default: return createTraceVis("<chk.name>", t);
      } 
    } 
  }
  
  Content showModuleVis(Module _, loc file) = createStateMachineVis(file.top);

  TModel typeCheckModule(Module m) {
    PathConfig pcfg = defaultPathConfig(m@\loc.top);
            
    Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
    TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true, refreshRoot = true, debug=true);
    
    return tr.tm;
  }
  
  void buildModule(Module m) {
    PathConfig pcfg = defaultPathConfig(m@\loc.top);
    PathConfig normPcfg = normalizerPathConfig(m@\loc.top);
            
    Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
    if (/unresolvedModule(QualifiedName qfn) := depGraph) {
      println("`<qfn>` could not be resolved yet, stopped the building process");
      return;
    }
    
    NormalizedResult nr = normalizeAndCheck(m, depGraph, pcfg, normPcfg);
    translateSnippets(nr.normMod, nr.normDepGraph, normPcfg);    
  }
  
  return {
    annotator(Module (Module m) {
      loc proj = project(m@\loc.top);

      TModel tm = typeCheckModule(m);
      
      annotatedMod = m[@messages= {*tm.messages}];
      annotatedMod = annotatedMod[@hyperlinks=tm.useDef];
      
      return annotatedMod;
    }),
    builder(set[Message] (Module m) {
      buildModule(m);
      
      return {};
    }),
    syntaxProperties(#start[Module]),
    popup(
      menu("Rebel actions", [
        interaction("Visualize", showModuleVis), 
        interaction("Run check", runCheck)
      ])
    )   
  };
}