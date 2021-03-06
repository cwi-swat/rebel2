module rebel::checker::RebelToAlleTranslator

import rebel::lang::Syntax;
import rebel::lang::Parser;
import rebel::lang::TypeChecker;
import rebel::lang::DependencyAnalyzer;
 
import rebel::checker::translation::RelationsTranslator;
import rebel::checker::translation::ConstraintsTranslator;
import rebel::checker::translation::EventTranslator;
import rebel::checker::translation::FormulaAndExpressionTranslator;
import rebel::checker::translation::CommonTranslationFunctions;
import rebel::checker::ConfigTranslator;
import rebel::checker::translation::RelationCollector;
 
import util::PathUtil;

import IO;  
import Set;
import util::Benchmark;

alias TransResult = tuple[str alleSpec, int duration]; 

TransResult translateToAlleAlle(Config cfg, Module m, TModel tm, PathConfig pcfg, bool saveAlleAlleFile = true) {
  print("Translating Rebel to AlleAlle ...");
  int startTime = cpuTime();
  RelMapping rm = constructRelMapping(m, tm);

  set[Spec] spcs = {inst.spc | inst <- cfg.instances};
  
  str alleSpec = "<translateRelationDefinitions(cfg, tm)>
                 '<translateConstraints(cfg, spcs, tm, rm)>
                 '<translateFacts(m, rm, tm, spcs)>
                 '<translateAssert(m, rm, tm, spcs)>
                 '
                 '// Minimize the number of steps by minimizing the number of Configurations
                 'objectives: minimize Config[count()]";
  
  
  if (saveAlleAlleFile) {
    writeFile(addModuleToBase(pcfg.checks, m)[extension="alle"], alleSpec);
  }

  int duration = (cpuTime() - startTime) / 1000000;
  println("done, took: <duration> ms.");
  
  return <alleSpec, duration>;  
}  
          
str translateFacts(Module m, RelMapping rm, TModel tm, set[Spec] spcs) {
  int lastUnique = 0;
  int nxtUnique() { return lastUnique += 1;}
  Context ctx = ctx(rm, tm, spcs, true, defaultCurRel(), defaultStepRel(), nxtUnique);

  return "<for (/Spec s <- m.parts) {>// Facts from spec `<s.name>`
         '<for (Fact f <- s.facts) {>// Fact `<f.name>` 
         '<translate(f.form, ctx)>
         '<}><}>";
}

str translateAssert(Module m, RelMapping rm, TModel tm, set[Spec] spcs) {
  set[Assert] asserts = {as | /Assert as <- m.parts};
  if (size(asserts) > 1) {
    throw "There should be only one assert to translate";
  }
  
  int lastUnique = 0;
  int nxtUnique() { lastUnique += 1; return lastUnique; }
  Context ctx = ctx(rm, tm, spcs, true, defaultCurRel(), defaultStepRel(), nxtUnique);
  
  return "<for (Assert a <- asserts) {>// Assert `<a.name>`
         '<translate(a.form, ctx)><}>";
}   