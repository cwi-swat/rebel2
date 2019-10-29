module rebel::lang::CommonTypeChecker

import rebel::lang::CommonSyntax;
import util::PathUtil;

extend analysis::typepal::TypePal;

import List;

data AType
  = intType()
  | dateType()
  | stringType()
  | boolType()
  | voidType()
  | setType(AType elemType)
  | optionalType(AType elemType)
  | specType(str name)
  | stateType()
  | eventType(AType argTypes)
  | moduleType()
  ;

data ScopeRole
  = specScope()
  | eventScope()
  | quantScope()
  ;

data Phase
  = prePhase()
  | postPhase()
  ;
  
data IdRole
  = specId()
  | moduleId()
  | eventId()
  | eventVariantId()
  | stateId()
  | fieldId()
  | paramId()
  | quantVarId()
  ; 
    
data EventInfo
  = initialEvent()
  ;    

data PathRole
  = importPath()
  ;

str prettyAType(intType()) = "Integer";
str prettyAType(dateType()) = "Date";  
str prettyAType(boolType()) = "Boolean";
str prettyAType(specType(str name)) = "<name>";
str prettyAType(eventType(AType argTypes)) = "event <prettyAType(argTypes)>";
str prettyAType(voidType()) = "*";
str prettyAType(setType(AType elem)) = "set of <prettyAType(elem)>";

TModel rebelTModelFromTree(Tree pt, bool debug = false, PathConfig pathConf = pathConfig(pt@\loc)){
    if (pt has top) pt = pt.top;
 
    c = newCollector("collectAndSolve", pt, config = tconfig(getTypeNamesAndRole = rebelTypeNamesAndRole,
                                                             isSubType = subtype,
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

tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(specType(str name)) = <[name], {specId()}>;
default tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(AType t) = <[], {}>;

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
    
void collect(current: (Module)`<ModuleId modDef> <Import* imports> <Part+ parts>`, Collector c) { 
  c.define("<modDef.name>", moduleId(), current, defType(moduleType()));
  
  c.enterScope(current); 
    collect(imports, c);
    collect(parts, c);
  c.leaveScope(current);
} 

void collect(current:(Import) `import <QualifiedName moduleName>`, Collector c) {
  c.addPathToDef(moduleName, {moduleId()}, importPath());
  c.push(__REBEL_IMPORT_QUEUE, moduleName);
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

private void collectQuant([], Formula f, Collector c) { 
  collect(f, c);
}
  
private void collectQuant([Decl hd, *tl], Formula f, Collector c) {
    collect(hd, c);
    collectQuant(tl, f, c);
}


void collect(current: (Formula)`forall <{Decl ","}+ dcls> | <Formula frm>`, Collector c) {
  c.fact(current, boolType());

  c.enterScope(current);
    collectQuant([d | d <- dcls], frm, c);
  c.leaveScope(current);
}

void collect(current: (Formula)`exists <{Decl ","}+ dcls> | <Formula frm>`, Collector c) {
  c.fact(current, boolType());

  c.enterScope(current);
    collectQuant([d | d <- dcls], frm, c);
  c.leaveScope(current);
}

void collect(current: (Decl)`<{Id ","}+ vars> : <Expr expr>`, Collector c) {
  for (Id var <- vars) {
    c.define("<var>", quantVarId(), var, defTypeCall([expr@\loc], 
      AType (Solver s) {
        if (setType(AType elemType) := s.getType(expr)) {
          return elemType;
        } else {
          s.report(error(current, "Should be a set type but is %t", expr));
        }
      }));
  }
  
  collect(expr, c);
}

void collect(current: (Formula)`<Expr exp> is <Id state>`, Collector c) {
  c.calculate("is in state", current, [exp],
    AType (Solver s) {
      s.requireTrue(specType(_) := s.getType(exp),  
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
        case <intType(), intType()>: return boolType();
        default:
          s.report(error(f, "Equal types required, found %t and %t", lhs, rhs));
      }
      return boolType();
    });
}

private void collectEq(Collector c, Formula f, Expr lhs, Expr rhs, str explain) {
  c.calculate(explain, f, [lhs,rhs], 
    AType (Solver s) {
      s.requireSubType(lhs, rhs, error(f, "Expressions are not type compatible, found %t and %t", lhs, rhs));
      return boolType();
    });
}


void collect(current: (Formula)`<Expr lhs> = <Expr rhs>`, Collector c) {
  collectEq(c, current, lhs, rhs, "equality");
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> != <Expr rhs>`, Collector c) {
  collectEq(c, current, lhs, rhs, "inequality");
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
      s.requireEqual(expr, intType());
      return intType();
    });
    
  collect(expr, c);
}

void collect(current: (Expr)`now`, Collector c) {
  c.fact(current, dateType());
}

void collect(current: (Expr)`now.<Id field>`, Collector c) {
  c.fact(current, intType());
}

void collect(current: (Expr)`<Expr expr>'`, Collector c) {
  if (prePhase() := c.top("phase")) {
    c.report(error(current, "Can not reference post value in precondition"));
  }
  
  c.fact(current, expr);
  c.push("ref", postPhase);
  
  collect(expr, c);
}

void collect(current: (Expr)`<Expr lhs> + <Expr rhs>`, Collector c) {
  c.calculate("addition", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        case {setType(AType elem), elem}: return setType(elem);
        default:
          s.report(error(current, "`+` not defined for %t and %t", lhs, rhs));
      }
    });  
    
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> - <Expr rhs>`, Collector c) {
  c.calculate("subtraction", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        case {setType(AType elem), elem}: return setType(elem);
        default:
          s.report(error(current, "`-` not defined for %t and %t", lhs, rhs));
      }
    });    
  
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> * <Expr rhs>`, Collector c) {
  c.calculate("multiplication", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        default:
          s.report(error(current, "`*` not defined for %t and %t", lhs, rhs));
      }
    });  
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> / <Expr rhs>`, Collector c) {
  c.calculate("devision", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        default:
          s.report(error(current, "`/` not defined for %t and %t", lhs, rhs));
      }
    });  
    
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Id var>`, Collector c) {
  c.use(var, {paramId(), quantVarId()});
}

void collect(current: (Expr)`this.<Id fld>`, Collector c) {
  c.use(fld, {fieldId()});
  c.fact(current, fld);
}

void collect(current: (Expr)`<Lit l>`, Collector c) {
  collect(l, c); 
}

void collect(current: (Lit)`<Int i>`, Collector c) {
  c.fact(current, intType());
}

void collect(current: (Lit)`<StringConstant s>`, Collector c) {
  c.fact(current, stringType());
}

void collect(current: (Lit)`{}`, Collector c) {
  c.fact(current, setType(voidType()));
}

void collect(current: (Type)`<TypeName tp>`, Collector c) {
  collect(tp,c);
}

void collect(current: (Type)`set <TypeName tp>`, Collector c) {
  c.calculate("set", current, [tp],
    AType (Solver s) {
      return setType(s.getType(tp));
    });

  collect(tp,c);
}

void collect(current: (Type)`?<TypeName tp>`, Collector c) {
  c.calculate("optional", current, [tp],
    AType (Solver s) {
      return optionalType(s.getType(tp));
    });

  collect(tp,c);
}

void collect(current: (TypeName)`Integer`, Collector c) {
  c.fact(current, intType());
}

void collect(current: (TypeName)`String`, Collector c) {
  c.fact(current, stringType());
}

void collect(current: (TypeName)`Date`, Collector c) {
  c.fact(current, dateType());
}

void collect(current: TypeName tn, Collector c) {
  c.use(tn, {specId()});
}

bool subtype(AType a, a) = true;
bool subtype(setType(voidType()), setType(_)) = true;
bool subtype(setType(_), setType(voidType())) = true;
bool subtype(setType(AType a), setType(AType b)) = subtype(a,b);

default bool subtype(AType a, AType b) = false; 