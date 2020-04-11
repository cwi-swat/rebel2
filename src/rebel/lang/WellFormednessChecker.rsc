module rebel::lang::WellFormednessChecker

import analysis::typepal::Collector;
import rebel::lang::CommonTypeChecker;
import rebel::lang::Syntax;

TModel checkWellFormedness(Module root, TModel tm) {
  tm = checkConfig(root, tm);
  
  return tm;
}
 
private TModel checkConfig(Module root, TModel tm) {
  for (/Config c <- root.parts) {
    // find all referenced types in the Config
    set[AType] declTypes = {tm.facts[t@\loc] | /Type t := c, t@\loc in tm.facts};
    tm.messages += [warning("Specification `<name>` is referenced by specifications but no instance is declared in the configuration", c@\loc) | AType t:specType(str name) <- tm.facts<1>, t notin declTypes]; 
  }
  
  return tm;
}