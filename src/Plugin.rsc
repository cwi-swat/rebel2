module Plugin

import lang::Syntax;
import lang::Parser;

import analysis::Checker;

import util::IDE;
import util::HtmlDisplay;
import util::Prompt;

import salix::App;
import vis::statemachine::StateMachineVis;

import ParseTree;

void main() {
  str REBEL2_LANGUAGE = "Rebel2 Language";
  //str REBEL2_TEST_LANGUAGE = "Rebel2 Test Language";

  registerLanguage(REBEL2_LANGUAGE,"rebel", parseSpec);
  //registerLanguage(REBEL_TEST_LANGUAGE, "tebel", parseTestModule);
  
  registerContributions(REBEL2_LANGUAGE, getRebelContributions());
}

alias VisConfig = tuple[int port, App[Model] app];

set[Contribution] getRebelContributions() {
  int startPort = 54840;
  int endPort = 54850;
  map[loc, VisConfig] runningVisInstances = ();
  list[int] visualisationPorts = [startPort..endPort];
 
  return {
    annotator(Spec (Spec s) {
      TModel tm = collectAndSolve(s);

      annotatedSpec = s[@messages= {m | m <- tm.messages}];
      annotatedSpec = annotatedSpec[@hyperlinks=tm.useDef];
      
      return annotatedSpec;
    }),
    syntaxProperties(#start[Spec]),
    popup(
      menu("Rebel actions", [
        action("Visualize", (Spec current, loc file) {
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
        })
      ])
    )   
  };
}