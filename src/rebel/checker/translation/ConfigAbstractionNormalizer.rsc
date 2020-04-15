module rebel::checker::translation::ConfigAbstractionNormalizer

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;

import rebel::checker::translation::CommonTranslationFunctions;

import IO;
import ParseTree;
import analysis::graph::Graph;

alias AbstractionResult = tuple[Config cfg, set[Spec] spcs]; 

AbstractionResult filterAbstractions(str config, set[Module] allMods, TModel tm) {
  Graph[Spec] spcDepGraph = extractSpecDependencyGraph(allMods, tm);

  bool replace(Type abstractSpcType, Type concreteSpcType) {
    Spec abstractSpc = lookupSpecByRef(abstractSpcType@\loc, allMods, tm);
    Spec concreteSpc = lookupSpecByRef(concreteSpcType@\loc, allMods, tm);
    
    Spec filteredSpc = visit(abstractSpc) {
      case Type t => concreteSpcType when "<t>" == "<abstractSpcType>"
      case Expr e => [Expr]"<concreteSpcType>" when "<e>" == "<abstractSpcType>"
    }; 
    
    filteredSpc.name = concreteSpc.name;
    
    allMods = visit(allMods) {
      case Spec s => filteredSpc when s == abstractSpc
    };
    
    spcDepGraph += {<f,abstractSpc> | <f,t> <- spcDepGraph, t == concreteSpc};
    spcDepGraph = {<f,t> | <Spec f, Spec t> <- spcDepGraph, f != concreteSpc, t != concreteSpc};
  
    // Check whether some specs have become `detatched`. If so, remove them.
    components = connectedComponents(spcDepGraph);
    for (set[Spec] component <- components, /abstractSpc !:= component) {
      spcDepGraph -= {<f,t> | <f,t> <- spcDepGraph, f in component || t in component};
    }
    
    return true;
  }  
  
  if (Module m <- allMods, /rebel::lang::Syntax::Config cfg <- m.parts, "<cfg.name>" == config) {
    rebel::lang::Syntax::Config filteredCfg = visit (cfg) {
      case (InstanceSetup)`<{Id ","}+ labels> : <Type abstractSpc> abstracts <Type concreteSpc> <InState? inState> <WithAssignments? assignments>` =>
        (InstanceSetup)`<{Id ","}+ labels> : <Type concreteSpc> <InState? inState> <WithAssignments? assignments>` when replace(abstractSpc, concreteSpc)
    };  
    
    allMods = visit(allMods) {
      case rebel::lang::Syntax::Config c => filteredCfg when c == cfg
    };

    // Only keep those specs that are reachable from the root module
    return <filteredCfg, {f,t | <f,t> <- spcDepGraph}>;
  }
  
  throw "Unable to find Config";
}

private Spec lookupSpecByRef(loc specRef, set[Module] mods, TModel tm) {
  for (Module m <- mods, /Spec s <- m.parts, {s@\loc} == tm.useDef[specRef]) {
    return s;
  } 
  
  throw "Unable to find referenced Spec at `<specRef>`";
} 

private Spec lookupSpecByName(str spcName, set[Module] mods) {
  for (Module m <- mods, /Spec s <- m.parts, "<s.name>" == spcName) {
    return s;
  } 
  
  throw "Unable to find referenced Spec `<spcName>`";
} 

private Graph[Spec] extractSpecDependencyGraph(set[Module] mods, TModel tm) {
  Graph[Spec] spcDepGraph = {}; 

  for (Module m <- mods, /Spec s <- m.parts) {
   spcDepGraph += <s,s>;
    
    for (/Type t := s, !isPrim(t,tm)) {
      spcDepGraph += <s, lookupSpecByName("<t>", mods)>;
    }  
  }

  return spcDepGraph;
}

private void printSpcDepGraph(Graph[Spec] spcDepGraph) {
  for (Spec from <- spcDepGraph<0>, Spec to <- spcDepGraph[from]) {
    println("<from.name> -\> <to.name>"); 
  } 
}
