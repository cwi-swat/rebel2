module Plugin

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::Normalizer;
import rebel::checker::Rebel2Alle;
 
import util::IDE;
import util::HtmlDisplay;
import util::Prompt; 
import util::Maybe;  

import salix::App;
import vis::statemachine::StateMachineVis;

import ParseTree;
import Location;
import util::PathUtil; 

import IO; 

void main() {
  str REBEL2_LANGUAGE = "Rebel2 Language";
  registerLanguage(REBEL2_LANGUAGE,"rebel", parseModule);
  
  registerContributions(REBEL2_LANGUAGE, getRebelContributions());
}

alias VisConfig = tuple[int port, App[Model] app];

set[Contribution] getRebelContributions() {
  int startPort = 54840;
  int endPort = 54850;
  map[loc, VisConfig] runningVisInstances = ();
  list[int] visualisationPorts = [startPort..endPort];
 
  void runCheck(Module m, loc selection) {
    if (/Check chk <- m.parts, isContainedIn(selection, chk@\loc)) {
      println("Running check");
      performCheck(chk, m);  
    } 
  }
  
  void createStateMachineVis(Module current, loc file) {
    if (file.top notin runningVisInstances) {
      int port = startPort;
      
      while (file.top notin runningVisInstances && port < endPort) {
        try {
          App[Model] vis = createVis(file.top, port);
          vis.serve();
          runningVisInstances[file.top] = <port, vis>;
        } catch ex:  {
          port += 1;
        }
      }
    }
    
    if (file.top in runningVisInstances) {          
      htmlDisplay(|http://localhost/statemachine/index.html|[port = runningVisInstances[file.top].port]);
    } else {
      alert("Unable to start visualisation server, no port available");
    }            
  }

  TModel checkModule(Module m) {
    PathConfig pcfg = defaultPathConfig(m@\loc.top);
            
    Graph[RebelDependency] depGraph = calculateDependencies(m, pcfg);
    TypeCheckerResult tr = checkModule(m, depGraph, pcfg, saveTModels = true);
    
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

      TModel tm = checkModule(m);
      
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
        action("Visualize", createStateMachineVis), 
        action("Run check", runCheck)
      ])
    )   
  };
}