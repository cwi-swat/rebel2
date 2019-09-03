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

void translatePingPong() {
  Spec pp = parseSpec(|project://rebel2/examples/pingpong.rebel|);
  
  instances = {<pp, "p1", uninitialized()>, <pp, "p2", uninitialized()>};
  initialValues = {};  
  
  translateSpecs(<instances, initialValues, 20>);
}
//void translateCoffeeMachine() 
//  = translateSpecs({parseSpec(|project://rebel2/examples/CoffeeMachine.rebel|)});
  
void translateSpecs(Config config) {
  set[Spec] specs = {c.spc | c <- config.instances};
  str alleSpec = "<translateStaticPart(specs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(specs)>";
  
  writeFile(|project://rebel2/examples/latest-alle-spc.alle|, alleSpec);
}  