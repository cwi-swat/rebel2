module analysis::Rebel2Alle

import lang::Syntax;
import lang::Parser;
import analysis::StaticRelationsTranslator;
import analysis::DynamicRelationsTranslator;
import analysis::ConstraintsTranslator;
import analysis::CommonTranslationFunctions;

import String;
import IO;
import List;
import ParseTree;

//data State 
//  = uninitialized()
//  | finalized()
//  | state(str name)
//  ;
//  
//alias Config = tuple[rel[Spec spc, str instance, State initialState] initialStates, 
//                     rel[Spec spc, str instance, str field, str val] initialValues, 
//                     int numberOfTransitions];

// For testing
import analysis::Normalizer;

void translatePingPong() {
  Spec pp = parseSpec(|project://rebel2/examples/pingpong.rebel|);
  
  instances = {<pp, "p1", uninitialized()>, <pp, "p2", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(<instances, initialValues, 10>, "exists c: Config, p: StateVectorPingPongPrimitives | some (c |x| p) where times = 5");
}


void translateCoffeeMachine() {
  Spec c = normalize(parseSpec(|project://rebel2/examples/CoffeeMachine.rebel|));
  
  instances = {<c, "cm1", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(<instances, initialValues, 10>, "exists c: Config | (c |x| instanceInState)[state] in StateCoffeeMachineServe");
}


//void translateCoffeeMachine() 
//  = translateSpecs({parseSpec(|project://rebel2/examples/CoffeeMachine.rebel|)});
  
void translateSpecs(Config config, str check) {
  set[Spec] specs = {c.spc | c <- config.instances};
  str alleSpec = "<translateStaticPart(specs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(specs, check)>";
  
  writeFile(|project://rebel2/examples/latest-alle-spc.alle|, alleSpec);
}  