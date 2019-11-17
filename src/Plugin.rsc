module Plugin

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;

import analysis::allealle::Rebel2Alle;

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
  
  return {
    annotator(Module (Module m) {
      loc proj = project(m@\loc.top);
      
      TModel tm = rebelTModelFromTree(m, debug=false, pathConf = pathConfig(srcs = [ proj + "src", proj + "examples"]));

      annotatedMod = m[@messages= {*tm.messages}];
      annotatedMod = annotatedMod[@hyperlinks=tm.useDef];
      
      return annotatedMod;
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