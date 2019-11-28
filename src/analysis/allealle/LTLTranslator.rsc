module analysis::allealle::LTLTranslator

import analysis::allealle::CommonTranslationFunctions;
import analysis::allealle::EventTranslator;
import analysis::allealle::RelationCollector;
import analysis::allealle::FormulaAndExpressionTranslator;

import rebel::lang::Syntax;
import rebel::lang::TypeChecker;

import String;
import IO;
import Set;
import Map;
import List;

str translateAssert(str assertName, set[Module] mods, Config cfg) {
  if (Module m <- mods, /(Assert)`assert <Id name> = <Formula form>;` <- m.parts, "<name>" == assertName) {
    return "// Assert: <name>
           '<translate(form, ctx(cfg, defaultCurRel(), defaultStepRel()))>
           '<if (!cfg.finiteTrace) {>// Force infinite traces
           'some loop <}>
           '"; 
  }
}

str translateFacts(set[Module] mods, Config cfg) {
  list[str] alleFacts = ["// Fact: <f.name>
                        '<translate(f.form, ctx(cfg, defaultCurRel(), defaultStepRel()))>" | Module m <- mods, /Fact f <- m.parts];  

  return intercalate("\n", alleFacts);
}