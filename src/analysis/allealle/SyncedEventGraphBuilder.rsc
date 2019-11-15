module analysis::allealle::SyncedEventGraphBuilder

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;
import analysis::allealle::CommonTranslationFunctions;

extend analysis::graphs::Graph;
import IO;

alias SyncedWith = tuple[Spec s, Event e];

Graph[SyncedWith] buildSyncGraph(set[Spec] spcs, TModel tm) {
  Spec findSpecByName(str name) = s when Spec s <- spcs, "<s.name>" == name;
  Event findEventByName(str name, Spec s) = e when Event e <- s.events, "<e.name>" == name;

  Graph[SyncedWith] syncDep = {};
   
  for (Spec s <- spcs, Event e <- s.events, /(Formula)`<Expr exp>.<Id ev>(<{Expr ","}* args>)` := e.body, specType(str spcName) := getType(exp,tm)) {
    Spec otherSpec = findSpecByName(spcName);
    Event otherEvent = findEventByName("<ev>", otherSpec);
    
    syncDep += <<s,e>,<otherSpec, otherEvent>>;             
  }
  
  return syncDep;
}

str toStr(tuple[SyncedWith from, SyncedWith to] n) = "<toStr(from)> -\> <toStr(to)>";
str toStr(SyncedWith sw) = "<sw.s.name>.<sw.e.name>";
