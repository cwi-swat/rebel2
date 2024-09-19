module rebel::checker::tests::AlleAlleTranslatorTester

import util::PathUtil;
import rebel::checker::CheckAssembler;
import rebel::checker::Normalizer;
import rebel::checker::RebelToAlleTranslator;
import rebel::checker::ConfigTranslator;
import rebel::lang::Syntax;
import rebel::lang::Parser;

import String;

private loc root() = |home:///develop/workspace/personal/rebel2|;

void testTranslateLimitCheckSmall() = testTranslateToAlleAlle("CanInitializeLimit", root() + "examples/paper/debitcard/checks/LimitChecksWithoutMocks.rebel");
void testTranslateLimitCheckBig() = testTranslateToAlleAlle("CantOverdrawLimit", |project://rebel2/examples/paper/debitcard/checks/LimitChecksWithoutMocks.rebel|);

void testTranslateToAlleAlle(str check, loc modul) {
  PathConfig pcfg = defaultPathConfig(modul);

  Module m = parseModule(modul);
  
  gen = assembleCheck(check, m, pcfg);
  norm = normalizeAndTypeCheck(gen.m, gen.tm, pcfg, saveNormalizedMod=true);
  
  Check chk = findCheckByName(check, m);
  tuple[int,bool] steps = findSearchDepth(chk.depth);
  cfgRes = buildConfig(findConfigByName("<chk.config>",norm.m), norm.m, norm.tm, steps<0>, steps<1>, /(Objective)`infinite trace` := chk);

  // Step 4: Translate the normalized, combined module to an AlleAlle specification
  TransResult transRes = translateToAlleAlle(cfgRes.cfg, norm.m, norm.tm, pcfg);
}

private rebel::lang::Syntax::Config findConfigByName(str cfgName, Module m) {
  for ((Part)`<Config cfg>` <- m.parts, "<cfg.name>" == cfgName) {
    return cfg;
  } 
  
  throw "Unable to find referenced Config at `<chk.config@\loc>`";
}

private tuple[int,bool] findSearchDepth((SearchDepth)`max <Int steps> steps`) = <toInt("<steps>") + 1, false>;
private tuple[int,bool] findSearchDepth((SearchDepth)`exact <Int steps> steps`) = <toInt("<steps>") + 1, true>;

private Check findCheckByName(str check, Module m) {
  if ((Part)`<Check chk>` <- m.parts, "<chk.name>" == check) {
    return chk;
  }
  
  throw "Unable to find check with name `<check>`"; 
}
