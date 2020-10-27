module rebel::lang::tests::RebelSlocCounter

import rebel::lang::Syntax;
import rebel::lang::Parser;

import String;
import IO;

void countAndPrintSlocs(set[loc] rebelMods) {
  lrel[str,int] slocs = countSlocs(rebelMods);
  
  int total = 0;
  for (spc <- slocs<0>, int sloc <- slocs[spc]) {
    println("<spc>: <sloc> SLOC");
    total += sloc;
  }
  
  println("Total SLOC: <total>");
}

lrel[str,int] countSlocs(set[loc] rebelMods) {
  lrel[str,int] result = [];

  for (m <- rebelMods) {
    result += countSloc(m);
  }
  
  return result;
}

lrel[str,int] countSloc(loc rebelMod) {
  lrel[str,int] result = [];
  Module m = parseModule(rebelMod);
  
  // 1.find specs
  for ((Part)`<Spec spc>` <- m.parts) {
    //  only count non empty, non comment lines
    list[str] lines = split("\n","<spc>");
    int sloc = (0 | it + 1 | line <- lines, trim(line) != "", !startsWith(trim(line), "//")); 

    result += <"<m.\module.name> - <spc.name>", sloc>;
  }
  
  return result;
}