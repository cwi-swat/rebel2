module rebel::checker::tests::AssemblerTester

import util::PathUtil;
import rebel::checker::CheckAssembler;

void testAssemblyScen6Step3() = testCheckAssembly("UpToStep3", |project://rebel2/examples/paper/els/Scenario6.rebel|);

void testCheckAssembly(str check, loc modul) {
  PathConfig pcfg = defaultPathConfig(modul);

  assembleCheck(check, modul, pcfg);
}