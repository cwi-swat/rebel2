module analysis::allealle::Rebel2Alle

import lang::Syntax;
import lang::Parser;
import analysis::allealle::StaticRelationsTranslator;
import analysis::allealle::DynamicRelationsTranslator;
import analysis::allealle::ConstraintsTranslator;
import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;
  
import IO;  
  
void translateSpecs(Config config, TModel tm, str check) {
  set[Spec] specs = {c.spc | c <- config.instances};
  str alleSpec = "<translateStaticPart(specs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(specs, tm, check)>";
  
  writeFile(|project://rebel2/examples/latest-alle-spc.alle|, alleSpec);
}  