module rebel::checker::tests::NormalizerTester

import util::PathUtil;
import rebel::checker::CheckAssembler;
import rebel::checker::Normalizer;

void testNormalizingScen6Step3() = testNormalize("UpToStep3", |project://rebel2/examples/paper/els/Scenario6.rebel|);

void testNormalizeLimitCheckSmall() = testNormalize("CanInitializeLimit", |project://rebel2/examples/local/debitcard/checks/LimitChecksWithoutMocks.rebel|);
void testNormalizeLimitCheckBig() = testNormalize("CantOverdrawLimit", |project://rebel2/examples/local/debitcard/checks/LimitChecksWithoutMocks.rebel|);

void testNormalize(str check, loc modul) {
  PathConfig pcfg = defaultPathConfig(modul);

  gen = assembleCheck(check, modul, pcfg);
  normalizeAndTypeCheck(gen.m, gen.tm, pcfg, saveNormalizedMod=true);
}
