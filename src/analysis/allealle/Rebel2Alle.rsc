module analysis::allealle::Rebel2Alle

import lang::Syntax;
import lang::Parser;
import analysis::allealle::StaticRelationsTranslator;
import analysis::allealle::DynamicRelationsTranslator;
import analysis::allealle::ConstraintsTranslator;
import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;

import ide::CombinedModelFinder; // From AlleAlle
import ide::CombinedSyntax;      // From AlleAlle
import ide::Parser;              // From AlleAlle
import ide::CombinedAST;
import ide::CombinedImploder;
  
import IO;  
  
void translateSpecs(Config config, str check, bool debug = true) {
  set[Spec] specs = {inst.spc | inst <- config.instances};
  str alleSpec = "<translateStaticPart(specs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(specs, config, check)>";
  
  if (debug) {
    writeFile(|project://rebel2/examples/latest-alle-spc.alle|, alleSpec);
  }
  
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec));

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    stop();
  }
}  

//data ModelAttribute
//  = idAttribute(str name, str id)
//  | fixedAttribute(str name, Term val)
//  | varAttribute(str name, Term val, str smtVarName)
//  ;
//  
//data ModelTuple
//  = fixedTuple(list[ModelAttribute] attributes)
//  | varTuple(list[ModelAttribute] attributes, str smtVarName)
//  ;  
//
//data ModelRelation 
//  = mRelation(str name, Heading heading, list[ModelTuple] tuples)
//  ;
//    
//data Model 
//  = model(set[ModelRelation] relations)
//  | empty()
//  ;

data Trace
  = step(Configuration cur, Configuration next, RaisedEvent re, Trace next)
  | empty()
  ;

data Configuration 
  = config(rel[Spec spc, str instance, State state] instances, rel[Spec spc, str instance, str field, set[str] val] values)
  ;
  