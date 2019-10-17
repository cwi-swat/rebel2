module analysis::allealle::tests::RebelSIETester

import analysis::allealle::Rebel2Alle;

import lang::Syntax;
import lang::Parser;

import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;

import String;
import IO;
import List;
import ParseTree;

import analysis::Normalizer;
import util::PathUtil;

void testSIE_WithdrawAfterDeposit() {
  loc normAccountFile = |project://rebel2/bin/normalized/local/sie/Account.rebel|;
  
  normalize(parseModule(|project://rebel2/examples/local/sie/Account.rebel|));
  
  Module normAccount = parseModule(normAccountFile);
  
  TModel tm = rebelTModelFromTree(normAccount, debug = false, pathConf = normPathConfig());
  
  instances = {<getSpec(normAccount, "Account"), "a1", uninitialized()>,
               <getSpec(normAccount, "Account"), "a2", uninitialized()>};

  translateSpecs(config(instances, {}, tm, 10),
    "∃ o1 ∈ order, o2 ∈ (order ⨝ o1[nxt-\>cur]), o3 ∈ (order ⨝ o2[nxt-\>cur]), a1 ∈ (Instance ⨝ Account)[instance], a2 ∈ (Instance ⨝ Account)[instance] ∖ a1 | 
    '  let c1 = o1[cur-\>config], c2 = o1[nxt-\>config], c3 = o2[nxt-\>config] | 
    '    (((o1 ⨝ raisedEvent ⨝ a1)[event] = EventAccountDeposit) ∧ 
    '    some ((c1 ⨝ SVAccountOnePrims ⨝ a1)[balance-\>a1Balance] ⨯ (c3 ⨝ SVAccountOnePrims ⨝ a2)[balance-\>a2Balance]) where a1Balance = a2Balance ∧ 
    '    (c1 ⨝ instanceInState ⨝ a1)[state] = (c3 ⨝ instanceInState ⨝ a2)[state]) ∧ 
    '
    '    some ((ParamsEventAccountWithdrawPrimitives ⨝ o3)[amount-\>newAmount] ⨯ (ParamsEventAccountWithdrawPrimitives ⨝ o2)[amount-\>oldAmount]) where newAmount = oldAmount ∧ 
    '    
    '    ((o2 ⨝ raisedEvent ⨝ a1)[event] = EventAccountWithdraw) ∧ 
    '    ¬ (let curAccountFlattened = (SVAccountOnePrims ⨝ o3[cur -\> config] ⨝ a2)[balance-\>curBalance],
    '         paramAccountWithdrawFlattened = (o3 ⨝ ParamsEventAccountWithdrawPrimitives)[amount] |
    '          ( 
    '            // Preconditions 
    '            (some (paramAccountWithdrawFlattened) where (amount \> 0)) ∧
    '            (some (curAccountFlattened ⨯ paramAccountWithdrawFlattened) where (curBalance  -  amount \>= 0)) 
    '          ) 
    '    )
    '");        
}

void testSIE_DepositAfterDeposit() {
  loc normAccountFile = |project://rebel2/bin/normalized/local/sie/Account.rebel|;
  
  normalize(parseModule(|project://rebel2/examples/local/sie/Account.rebel|));
  
  Module normAccount = parseModule(normAccountFile);
  
  TModel tm = rebelTModelFromTree(normAccount, debug = false, pathConf = normPathConfig());
  
  instances = {<getSpec(normAccount, "Account"), "a1", uninitialized()>,
               <getSpec(normAccount, "Account"), "a2", uninitialized()>};

  translateSpecs(config(instances, {}, tm, 10),
    "∃ o1 ∈ order, o2 ∈ (order ⨝ o1[nxt-\>cur]), o3 ∈ (order ⨝ o2[nxt-\>cur]), a1 ∈ (Instance ⨝ Account)[instance], a2 ∈ (Instance ⨝ Account)[instance] ∖ a1 | 
    '  let c1 = o1[cur-\>config], c2 = o1[nxt-\>config], c3 = o2[nxt-\>config] | 
    '    // exists deposit: Deposit, c1,c2,c3: Config | deposit(c1,c2) && (deposit(c2,c3) \<=\> pre_deposit(c1,c3))
    '    (((o1 ⨝ raisedEvent ⨝ a1)[event] = EventAccountDeposit) ∧ 
    '    some ((c1 ⨝ SVAccountOnePrims ⨝ a1)[balance-\>a1Balance] ⨯ (c3 ⨝ SVAccountOnePrims ⨝ a2)[balance-\>a2Balance]) where a1Balance = a2Balance ∧ 
    '    (c1 ⨝ instanceInState ⨝ a1)[state] = (c3 ⨝ instanceInState ⨝ a2)[state]) ∧ 
    '
    '    (some ((ParamsEventAccountDepositPrimitives ⨝ o3)[amount-\>newAmount] ⨯ (ParamsEventAccountDepositPrimitives ⨝ o2)[amount-\>oldAmount]) where newAmount = oldAmount ∧ 
    '    ((o2 ⨝ raisedEvent ⨝ a1)[event] = EventAccountDeposit))  ∧ 
    '    ¬(let paramAccountDepositFlattened = (o3 ⨝ ParamsEventAccountDepositPrimitives)[amount] |
    '          ( 
    '            // Preconditions 
    '            (some (paramAccountDepositFlattened) where (amount \> 0))
    '          ) 
    '    )
    '");        
}


private PathConfig normPathConfig() = pathConfig(srcs=[|project://rebel2/bin/normalized|]);

Spec getSpec(Module m, str specName) {
  for ((Part)`<Spec spc>` <- m.parts, "<spc.name>" == specName) {
    return spc;
  }
  
  throw "Unable to find spec with name `<specName>` in file `<m@\loc.top>`"; 
}
