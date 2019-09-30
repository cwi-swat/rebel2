module analysis::Checker

import lang::Syntax;

extend analysis::typepal::TypePal;

data AType
  = intType(AMult mult)
  | dateType()
  | boolType()
  | stateType()
  | eventType(AType argTypes)
  | specType(AMult mult, str name)
  | moduleType()
  ;

data AMult
  = oneMult()
  | loneMult()
  | setMult()
  ;

data Phase
  = prePhase()
  | postPhase()
  ;
  
data ScopeRole
  = specScope()
  | eventScope()
  ;
  
data IdRole
  = specId()
  | moduleId()
  | eventId()
  | eventVariantId()
  | stateId()
  | fieldId()
  | paramId()
  ; 
    
data EventInfo
  = initialEvent()
  ;    

data PathRole
  = importPath()
  ;
   
str prettyAType(intType(AMult mult)) = "<prettyAMult(mult)> Integer";
str prettyAType(dateType()) = "Date";  
str prettyAType(boolType()) = "Boolean";
str prettyAType(specType(AMult mult, str name)) = "<prettyAMult(mult)> <name>";
str prettyAType(eventType(AType argTypes)) = "event <prettyAType(argTypes)>";

str prettyAMult(oneMult()) = "one";
str prettyAMult(loneMult()) = "lone";
str prettyAMult(setMult()) = "set";

TModel rebelTModelFromTree(Tree pt, bool debug = false, PathConfig pathConf = pathConfig(pt@\loc)){
    if (pt has top) pt = pt.top;
 
    c = newCollector("collectAndSolve", pt, config = tconfig(getTypeNamesAndRole = rebelTypeNamesAndRole,
                                                             verbose=debug, 
                                                             logTModel = debug, 
                                                             logAttempts = debug, 
                                                             logSolverIterations= debug, 
                                                             logSolverSteps = debug));  

    collect(pt, c);
    handleImports(c, pt, pathConf);
    
    TModel model = newSolver(pt, c.run()).run();
    return model;
}

tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(specType(AMult mult, str name)) = <[name], {specId()}>;
default tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(AType t) = <[], {}>;

private loc project(loc file) {
   assert file.scheme == "project";
   return |project://<file.authority>|;
}

data PathConfig = pathConfig(list[loc] srcs = [], list[loc] libs = []);

PathConfig pathConfig(loc file) {
   assert file.scheme == "project";

   p = project(file);      
 
   return pathConfig(srcs = [ p + "src", p + "examples"]);
}

private str __REBEL_IMPORT_QUEUE = "__rebelImportQueue";

str getFileName((QualifiedName) `<{Id "::"}+ moduleName>`) = replaceAll("<moduleName>.rebel", "::", "/");

tuple[bool, loc] lookupModule(QualifiedName name, PathConfig pcfg) {
    for (s <- pcfg.srcs) {
        result = (s + replaceAll("<name>", "::", "/"))[extension = "rebel"];
        println(result);
        if (exists(result)) {
          return <true, result>;
        }
    }
    return <false, |invalid:///|>;
}

void handleImports(Collector c, Tree root, PathConfig pcfg) {
    set[QualifiedName] imported = {};
    
    while (list[QualifiedName] modulesToImport := c.getStack(__REBEL_IMPORT_QUEUE) && modulesToImport != []) {
      c.clearStack(__REBEL_IMPORT_QUEUE);
      
        for (m <- modulesToImport, m notin imported) {
          if (<true, l> := lookupModule(m, pcfg)) {
                collect(parse(#start[Module], l).top, c);
            }
            else {
              c.report(error(m, "Cannot find module %v in %v", "<m>", pcfg.srcs));
            }
            imported += m; 
        }
    }
}
    
void collect(current: (Module)`<ModuleId modDef> <Import* imports> <Spec spc>`, Collector c) { 
  c.define("<modDef.name>", moduleId(), current, defType(moduleType()));
  
  c.enterScope(current); 
    collect(imports, c);
    collect(spc, c);
  c.leaveScope(current);
}  

void collect(current: (Spec)`spec <Id name> <Fields? fields> <Constraints? constraints> <Event* events> <States? states>`, Collector c) {
  c.define("<name>", specId(), current, defType(specType(oneMult(), "<name>")));
  
  c.enterScope(current); 
       
    if (/Fields flds <- fields) {
      collect(flds.fields, c);
    }  
    
    collect(events, c);
    if (/States sts <- states) {
      collectStates(sts,c);
      collect(sts.trans, c);
    }
  
  c.leaveScope(current);
}

void collect(current:(Import) `import <QualifiedName moduleName>`, Collector c) {
  c.addPathToDef(moduleName, {moduleId()}, importPath());
  c.push(__REBEL_IMPORT_QUEUE, moduleName);
}

void collect(current: (Field)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", fieldId(), name, defType(tipe));
  collect(tipe, c);
}

void collectStates(States sts, Collector c) {
  set[State] done = {};
  
  visit(sts) {
    case (Transition)`<State from> -\> <State to> : <{TransEvent ","}+ events>;`: {
      if (from notin done) {
        c.define("<from>", stateId(), from, defType(stateType()));
        done += from;
      } else {
        c.use(from, {stateId()});
      }         
    }
  }
  
  // add an 'initialized' state
  c.define("initialized", stateId(), sts, defType(stateType()));
}

void collect(current: (Transition)`<State from>-\><State to> : <{TransEvent ","}+ events>;`, Collector c) {
  // 'from' was done earlier
  collect(to,c);
  collect(events,c);
}

void collect(current: (Transition)`<State super> <InnerStates? inner> { <Transition* trans> }`, Collector c) {
  collect(super,c);
  
  if (/InnerStates inn := inner) {
    collect(inn.states,c);   
  }
  
  collect(trans,c);
}

void collect((TransEvent)`<Id event>`, Collector c) {
  c.use(event, {eventId()});
}

void collect(current: (TransEvent)`<Id event>::<Id variant>`, Collector c) {
  c.useQualified(["<event>","<variant>"], variant, {eventVariantId()}, {eventId()});
}

void collect((TransEvent)`empty`, Collector c) {}

void collect(current: (State)`<Id name>`, Collector c) {
  c.use(name, {stateId()});
}

void collect(current: (State)`(*)`, Collector c) {}

void collect(current: (Event)`<Initial? init> event <Id name>(<{FormalParam ","}* formals>) <EventBody body>`, Collector c) {
  list[Id] fp = [f.name | f <- formals];
  
  c.define("<name>", eventId(), name, defType(fp, 
    AType (Solver s) {
      return eventType(atypeList([s.getType(f) | f <- fp]));
    }));
  
  c.enterScope(current);
    c.push("eventName", "<name>");
    
    if (/(Initial)`init` := init) {
      c.setScopeInfo(c.getScope(), eventScope(), initialEvent());
    }
      
    collect(formals, body, c);

    c.pop("eventName");
    
  c.leaveScope(current);
}

void collect(current: (EventVariant)`<Outcome outcome> <Id name> <EventBody body>`, Collector c) {
  c.fact(current, boolType());
  c.define("<name>", eventVariantId(), name, defType(current));
  
  c.enterScope(current); 
    collect(body, c);
  c.leaveScope(current);
}


void collect(current: (FormalParam)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", paramId(), name, defType(tipe));
  collect(tipe, c);
} 

void collect((EventBody)`<Pre? maybePre> <Post? maybePost> <EventVariant* variants>`, Collector c) {
  if (/Pre pre := maybePre) {
    c.push("phase", prePhase());
    
    for (Formula f <- pre.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");
  }
  
  if (/Post post := maybePost) {
    c.push("phase", postPhase());
  
    for (Formula f <- post.formulas) {
      collect(f, c);
    }
    
    c.pop("phase");    
  }
  
  collect(variants, c);
}

void collect(current: (Formula)`( <Formula f> )`, Collector c) {
  c.fact(current, f);
  collect(f, c);
}

void collect(current: (Formula)`<Formula lhs> && <Formula rhs>`, Collector c) {
  c.fact(current, boolType());
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Formula lhs> || <Formula rhs>`, Collector c) {
  c.fact(current, boolType());
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Formula lhs> =\> <Formula rhs>`, Collector c) {
  c.fact(current, boolType());
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Formula lhs> \<=\> <Formula rhs>`, Collector c) {
  c.fact(current, boolType());
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr spc>.<Id event>(<{Expr ","}* arguments>)`, Collector c) {
  c.useViaType(spc, event, {eventId()});
  
  args = [arg | arg <- arguments];
  
  c.calculate("raise event <event>", current, event + args, 
    AType (Solver s) {
      eType = s.getType(event);
      
      if (eventType(formalTypes) := s.getType(event)) {
        argTypes = atypeList([s.getType(a) | a <- args]);
        s.requireEqual(argTypes, formalTypes, 
          error(current, "Expected arguments %t, found %t", formalTypes, argTypes)); 
      } else {
        s.report(error(current, "Event expected, found %t", eType));
      }
      
      return boolType();
    });
  
  
  collect(spc, arguments, c);
}

void collect(current: (Formula)`<Expr exp> is <Id state>`, Collector c) {
  c.calculate("is in state", current, [exp],
    AType (Solver s) {
      s.requireTrue(specType(_,_) := s.getType(exp),  
                    error(current, "Can only perform an \'is\' operation on a specification"));
        
      return boolType();
    });

  c.useViaType(exp, state, {stateId()});

  collect(exp,c);
}

private void collectIntEq(Collector c, Formula f, Expr lhs, Expr rhs, str explain) {
  c.calculate(explain, f, [lhs,rhs], 
    AType (Solver s) {
      switch(<s.getType(lhs), s.getType(rhs)>){
        case <intType(oneMult()), intType(oneMult())>: return boolType();
        default:
          s.report(error(f, "Equal types required, found %t and %t", lhs, rhs));
      }
      return boolType();
    });
}

private void collectEq(Collector c, Formula f, Expr lhs, Expr rhs, str explain) {
  c.calculate(explain, f, [lhs,rhs], 
    AType (Solver s) {
      s.requireEqual(lhs, rhs, error(f, "Equal types required, found %t and %t", lhs, rhs));
      return boolType();
    });
}


void collect(current: (Formula)`<Expr lhs> = <Expr rhs>`, Collector c) {
  collectEq(c, current, lhs, rhs, "equality");
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> \> <Expr rhs>`, Collector c) {
  collectIntEq(c, current, lhs, rhs, "greater than");
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> \>= <Expr rhs>`, Collector c) {
  collectIntEq(c, current, lhs, rhs, "greater than equal");
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> \< <Expr rhs>`, Collector c) {
  collectIntEq(c, current, lhs, rhs, "lesser than");
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> \<= <Expr rhs>`, Collector c) {
  collectIntEq(c, current, lhs, rhs, "lesser than equal");
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`(<Expr expr>)`, Collector c) {
  c.fact(current, expr);
  collect(expr, c);
}

void collect(current: (Expr)`- <Expr expr>`, Collector c) {
  c.calculate("sign", current, [expr], 
    AType (Solver s) {
      s.requireEqual(expr, intType(oneMult()));
      return intType(oneMult());
    });
    
  collect(expr, c);
}

void collect(current: (Expr)`<Expr expr>`, Collector c) {
  c.fact(current, dateType());
}

void collect(current: (Expr)`<Expr expr>'`, Collector c) {
  if (prePhase() := c.top("phase")) {
    c.report(error(current, "Can not reference post value in precondition"));
  }
  
  c.fact(current, expr);
  c.push("ref", postPhase);
  
  collect(expr, c);
}

private void collectBinIntOp(Collector c, Expr expr, Expr lhs, Expr rhs, str explain, str op) {
  c.calculate(explain, expr, [lhs, rhs],
    AType (Solver s) {
      switch(<s.getType(lhs), s.getType(rhs)>){
        case <intType(oneMult()), intType(oneMult())>: return intType(oneMult());
        default:
          s.report(error(expr, "`<op>` not defined for %t and %t", lhs, rhs));
      }
    });    
}

void collect(current: (Expr)`<Expr lhs> + <Expr rhs>`, Collector c) {
  collectBinIntOp(c, current, lhs, rhs, "addition", "+");
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> - <Expr rhs>`, Collector c) {
  collectBinIntOp(c, current, lhs, rhs, "substraction", "-");
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> * <Expr rhs>`, Collector c) {
  collectBinIntOp(c, current, lhs, rhs, "multiplication", "*");
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> - <Expr rhs>`, Collector c) {
  collectBinIntOp(c, current, lhs, rhs, "division", "\\");
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Id var>`, Collector c) {
  c.use(var, {paramId()});
}

void collect(current: (Expr)`this.<Id fld>`, Collector c) {
  c.use(fld, {fieldId()});
  c.fact(current, fld);
}

void collect(current: (Expr)`<Lit l>`, Collector c) {
  collect(l, c); 
}

void collect(current: (Lit)`<Int i>`, Collector c) {
  c.fact(current, intType(oneMult()));
}

void collect(current: (Type)`<TypeName tp>`, Collector c) {
  c.push("mult", oneMult());
  collect(tp, c);
}

void collect(current: (Type)`<Multiplicity mult> <TypeName tp>`, Collector c) {
  c.push("mult", getMultiplicity(mult));
  collect(tp,c);
}

AMult getMultiplicity((Multiplicity)`one`) = oneMult();
AMult getMultiplicity((Multiplicity)`lone`) = loneMult();
AMult getMultiplicity((Multiplicity)`set`) = setMult();

void collect(current: (TypeName)`Integer`, Collector c) {
  c.fact(current, intType(c.pop("mult")));
}

void collect(current: TypeName tn, Collector c) {
  //c.fact(current, specType(c.pop("mult"), "<tn>"));
  c.use(tn, {specId()});
}