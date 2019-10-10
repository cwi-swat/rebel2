module analysis::allealle::Rebel2Alle

import lang::Syntax;
import lang::Parser;
import analysis::allealle::StaticRelationsTranslator;
import analysis::allealle::DynamicRelationsTranslator;
import analysis::allealle::ConstraintsTranslator;
import analysis::allealle::CommonTranslationFunctions;
import analysis::Checker;
import util::PathUtil;

import ide::CombinedModelFinder; // From AlleAlle
import ide::CombinedSyntax;      // From AlleAlle
import ide::Parser;              // From AlleAlle
import ide::CombinedAST;         // From AlleAlle
import ide::CombinedImploder;    // From AlleAlle
import util::ModelPrinter;       // From AlleAlle
import smtlogic::Core;              // From AlleAlle
import smtlogic::Ints;              // From AlleAlle
  
import IO;  
import Set;
import String;
import util::Maybe;
  
void translateSpecs(Config config, str check, bool debug = true) {
  set[Spec] specs = {inst.spc | inst <- config.instances};
  str alleSpec = "<translateStaticPart(specs)>
                 '<translateDynamicPart(config)>
                 '<translateConstraints(specs, config, check)>";
  
  if (debug) {
    writeFile(project(getOneFrom(specs)@\loc.top) + "examples/latest-alle-spc.alle", alleSpec);
  }
  
  ModelFinderResult mfr = checkInitialSolution(implodeProblem(alleSpec));

  if (sat(Model currentModel, Model (Domain) nextModel, void () stop) := mfr) {
    stop();
    convert(currentModel, specs, config.instances<0,1>, config.tm);
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

Trace convert(Model alleModel, set[Spec] specs, rel[Spec spc, str instance] instances, TModel tm) {
  // find the numer of 'steps' (or 'configurations') in the alle alle model
  int nrOfConfigs = getNrOfConfigs(alleModel); 

  for (int i <- [1..nrOfConfigs+1]) {
    println("<i>: 
            '  <config2Str(getConfiguration(i, specs, instances, alleModel, tm))>");
  }  
}

int getNrOfConfigs(Model alleModel) {
  configRel = findRelation(alleModel, "Config");
  configRel.tuples = sort(configRel.tuples, bool (ModelTuple a, ModelTuple b) { return getNumber(a, "c") < getNumber(b, "c");});  
  
  int nrOfConfigs = getNumber(configRel.tuples[-1], "c");
  return nrOfConfigs;
}

int getNumber(fixedTuple([idAttribute(str _, str id)]), str prefix) = getNumber(id, prefix);
int getNumber(varTuple([idAttribute(str _, str id)], str _), str prefix) = getNumber(id, prefix);

int getNumber(str idVal, str prefix) = toInt(replaceFirst(idVal, prefix, ""));

Configuration getConfiguration(int step, set[Spec] specs, rel[Spec spc, str instance] instances, Model alleModel, TModel tm) {
  rel[Spec,str,State] states = {};
  rel[Spec,str,str,str] values = {};
  
  for (s <- specs) {
    states += getStateInConfig(step, s, instances[s], alleModel, tm);
    values += getValuesInConfig(step, s, instances[s], alleModel, tm);
  }
  
  return config(states, values);
}

ModelRelation findRelation(Model m, str name) {
  for (r:mRelation(name,  _, list[ModelTuple] _) <- m.relations) {
    return r;
  }
  
  throw "Unable to find relation with name `<name>` in found AlleAlle model";
}

rel[Spec spc, str instance, State state] getStateInConfig(int step, Spec spc, set[str] instances, Model alleModel, TModel tm) {
  rel[Spec,str,State] instanceStates = {};
  
  // check 'primitive' values, they are all in the 'flattened' relation
  ModelRelation r = findRelation(alleModel, "instanceInState");

  State getState(str inst) {
    for (t <- r.tuples) {
      if (/idAttribute("config", "c<step>") := t.attributes && /idAttribute("instance", inst) := t.attributes, /idAttribute("state", str curState) := t.attributes) {
        return parseState(curState);
      }
    }
    
    throw "Unable to find state for `<inst>` in step `<step>`";
  }
  
  State parseState("state_uninitialized") = uninitialized();
  State parseState("state_finalized") = finalized();
  default State parseState(str st) = state(substring(st, findLast(st, "_")+1));


  for (inst <- instances) {
    instanceStates += {<spc, inst, getState(inst)>};
  }
  
  return instanceStates;
}

rel[Spec spc, str instance, str field, str val] getValuesInConfig(int step, Spec spc, set[str instance] instances, Model alleModel, TModel tm) {
  rel[Spec,str,str,str] values = {};
    
  Maybe[str] getValue(ModelRelation r, str inst, str field) {
    for (t <- r.tuples) {
      if (/idAttribute("config", "c<step>") := t.attributes && /idAttribute("instance", inst) := t.attributes) {
        if (/fixedAttribute(field, Term val) := t.attributes) {
          return just(parseTerm(val));
        } else if (/varAttribute(field, Term val, _) := t.attributes) {
          return just(parseTerm(val));
        }
      }
    }
    
    return nothing();
  }
  
  str parseTerm(lit(Literal l)) = model2Str(l);
  str parseTerm(neg(Term t)) = "-<model2Str(t)>";
  str parseTerm(\int(int i)) = "<i>";
  
  list[Field] primFields = lookupOnePrimitiveFields(spc, tm);
  if (primFields != []) {
    ModelRelation r = findRelation(alleModel, "SV<getCapitalizedSpecName(spc)>OnePrims");

    for (Field f <- primFields, inst <- instances, just(str val) := getValue(r, inst, "<f.name>")) {
      values += <spc, inst, "<f.name>", val>;    
    }
  }
  
  return values;
}

private str config2Str(Configuration cfg) {
  str getVal({str v}) = v;
  default str getVal(set[str] val) = val;

  str result = "";
  for (Spec s <- cfg.instances<0>, str inst <- cfg.instances[s]<0>, State st <- cfg.instances[s,inst]) {
    result += "<inst> (<s.name>) in `<st>` : <intercalate(", ", ["<field> = <getVal(cfg.values[s,inst,field])>" | str field <- cfg.values[s,inst]<0>])>\n";  
  }
  return result;
}

data Trace
  = step(Configuration conf, RaisedEvent re, Trace next)
  | goal(Configuration conf)
  ;

data Configuration 
  = config(rel[Spec spc, str instance, State state] instances, rel[Spec spc, str instance, str field, str val] values)
  ;

data RaisedEvent;