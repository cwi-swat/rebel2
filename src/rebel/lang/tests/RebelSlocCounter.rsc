module rebel::lang::tests::RebelSlocCounter

import rebel::lang::Syntax;
import rebel::lang::Parser;

import String;

int countSloc(loc rebelMod, str spcName) {
  int sloc = 0;
  
  Module m = parseModule(rebelMod);
  
  // 1.find specs
  for ((Part)`<Spec spc>` <- m.parts, "<spc.name>" == spcName) {
    //  only count non empty, non comment lines
    list[str] lines = split("\n","<spc>");
    sloc = (0 | it + 1 | line <- lines, trim(line) != "", !startsWith(trim(line), "//")) - 1; 
  }
  
  return sloc;
}