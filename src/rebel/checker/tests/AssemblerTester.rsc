module rebel::checker::tests::AssemblerTester

import util::PathUtil;
import rebel::checker::CheckAssembler;

void testAssemblyScen6Step3() = testCheckAssembly("UpToStep3", |project://rebel2/examples/paper/els/Scenario6.rebel|);
void testAssemblyOBCheck() = testCheckAssembly("CanSettleInstruction", |project://rebel2/examples/paper/sepact/checks/OriginatorBankChecks.rebel|);


void testAssemblyLimitSmall() = testCheckAssembly("CanInitializeLimit", |project://rebel2/examples/local/debitcard/checks/LimitChecksWithoutMocks.rebel|);
void testAssemblyLimitBig() = testCheckAssembly("CantOverdrawLimit", |project://rebel2/examples/local/debitcard/checks/LimitChecksWithoutMocks.rebel|);


void testCheckAssembly(str check, loc modul) {
  PathConfig pcfg = defaultPathConfig(modul);

  assembleCheck(check, modul, pcfg);
}