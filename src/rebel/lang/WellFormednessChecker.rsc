module rebel::lang::WellFormednessChecker

import analysis::typepal::Collector;
import rebel::lang::CommonTypeChecker;
import rebel::lang::Syntax;

TModel checkWellFormedness(Module root, TModel tm) {
  //tm = checkConfig(root, tm);
  tm = checkModifiersAndUseOfEvents(root, tm);
  return tm;
}
 
private TModel checkConfig(Module root, TModel tm) {
  for (/Config c <- root.parts) {
    // find all referenced types in the Config
    set[AType] declTypes = {tm.facts[t@\loc] | /Type t := c, t@\loc in tm.facts};
    //tm.messages += [warning("Specification `<name>` is referenced by specifications but no instance is declared in the configuration", c@\loc) | AType t:specType(str name) <- tm.facts<1>, t notin declTypes]; 
  }
  
  return tm;
}

private TModel checkModifiersAndUseOfEvents(Module root, TModel tm) {
  set[loc] refEvents = {};
  
  set[loc] nonInit = {};
  set[loc] nonFinal = {};
  
  set[loc] uses = tm.useDef<0>;
  
  for ((Part)`<Spec  spc>` <- root.parts) {
    for (/States sts <- spc.states, /(Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;` := sts) {
      bool isInitial = "<from>" == "(*)";
      bool isFinal = "<to>" == "(*)"; 

      for (TransEvent evnt <- events, evnt@\loc in uses, loc def <- tm.useDef[evnt@\loc]) {
        refEvents += def;
        
        AType evntType = tm.facts[def];
        if (eventType(_,set[ModifierInfo] mods) := evntType) { 
          if (isInitial, initial() notin mods) {
            nonInit += def;
          } 
          if (isFinal, final() notin mods) {
            nonFinal += def;
          }
        }
      }      
    }
    
    for(Event evnt <- spc.events, eventType(_,set[ModifierInfo] mods) := tm.facts[evnt@\loc]) {
      // check if pre-conditions reference 'this' variables
      if (initial() in mods, /e:(Expr)`this.<Id fld>` := evnt.body.pre) {
        tm.messages += [error("Pre condition references `<fld>` but it is not initialized yet", e@\loc)];  
      }
      if (final() in mods, /e:(Expr)`this.<Id fld>` := evnt.body.post) {
        tm.messages += [error("Post condition references `<fld>` but it can not have a value after finalization", e@\loc)];  
      }
      
      bool referenced = evnt@\loc in refEvents;
      
      if (!referenced) {
        for (EventVariant evntVar <- evnt.body.variants) {
          referenced = referenced || evntVar@\loc in refEvents;
          if (evntVar@\loc notin refEvents) {
            tm.messages += [warning("Event variant is not referenced in the state definition", evntVar.name@\loc)];        
          }
        }
      }
            
      if (!referenced) {
        tm.messages += [warning("Event or its variants are not referenced in the state definition", evnt.name@\loc)];
      }   
      if (evnt@\loc in nonInit) {
        tm.messages += [warning("Event is used to trigger a transition from the initial state but it is not marked as such", evnt.name@\loc)];
      }
      if (evnt@\loc in nonFinal) {
        tm.messages += [warning("Event is used to trigger a transition to a final state but it is not marked as such", evnt.name@\loc)];
      }      
    } 
  }   
   
  return tm;
}
