module rebel::lang::CommonTypeChecker

import rebel::lang::CommonSyntax;

extend analysis::typepal::TypePal;

import IO;

data AType
  = intType()
  | stringType()
  | boolType()
  | voidType()
  | setType(AType elemType)
  | optionalType(AType elemType)
  | specType(str name)
  | specInstanceType(str specName)
  | stateType()
  | eventType(AType argTypes, set[ModifierInfo] mods)
  | moduleType()
  | factType()
  | predType(AType argTypes)
  | namedTypeList(list[tuple[str, AType]] ntl)
  | unknownType()
  ;

data ScopeRole
  = moduleScope()
  | specScope()
  | eventScope() 
  | funcScope()
  | predScope()
  | quantScope()
  | factScope()
  | assertScope() 
  | primedScope()
  ;

data Phase
  = prePhase()
  | postPhase()
  ;
  
data IdRole
  = specId()
  | specInstanceId()
  | moduleId()
  | eventId()
  | eventVariantId()
  | predId()
  | stateId()
  | fieldId()
  | paramId()
  | quantVarId()
  | instanceId()
  ; 

data ModifierInfo
  = initial()
  | final()
  | internal()
  ;
    
data PathRole
  = importPath()
  ;

str prettyAType(intType()) = "Integer";
str prettyAType(boolType()) = "Boolean";
str prettyAType(stringType()) = "String";
str prettyAType(specType(str name)) = "<name>";
str prettyAType(specInstanceType(str specName)) = "instance of <specName>";
str prettyAType(eventType(AType argTypes, set[ModifierInfo] mods)) = "event <prettyAType(argTypes)>";
str prettyAType(voidType()) = "*";
str prettyAType(setType(AType elem)) = "set of <prettyAType(elem)>";
str prettyAType(optionalType(AType elem)) = "?<prettyAType(elem)>";
str prettyAType(unknownType()) = "\<\<??\>\>";

tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(specType(str name)) = <[name], {specId()}>;
tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(optionalType(AType elem)) = rebelTypeNamesAndRole(elem);
default tuple[list[str] typeNames, set[IdRole] idRoles] rebelTypeNamesAndRole(AType t) = <[], {}>;

//private str __REBEL_IMPORT_QUEUE = "__rebelImportQueue";
    
void collect(current: (Module)`<ModuleId modDef> <Import* imports> <Part+ parts>`, Collector c) { 
  c.define("<modDef.name>", moduleId(), current, defType(moduleType()));
  
  c.enterScope(current); 
    collect(imports, c);
    collect(parts, c);
  c.leaveScope(current);
} 

void collect(current:(Import) `import <QualifiedName moduleName>`, Collector c) {
  c.addPathToDef(moduleName, {moduleId()}, importPath());
  //c.push(__REBEL_IMPORT_QUEUE, moduleName);
}

void collect(current: (Formula)`( <Formula f> )`, Collector c) {
  c.fact(current, f);
  collect(f, c);
}

void collect(current: (Formula)`!<Formula f>`, Collector c) {
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

void collect(current: (Formula)`if <Formula cond> then <Formula then> else <Formula els>`, Collector c) {
  c.fact(current, boolType());
  collect(cond, then, els, c);
}

void collect(current: (Formula)`if <Formula cond> then <Formula then>`, Collector c) {
  c.fact(current, boolType());
  collect(cond, then, c);
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
        } else if (specType(str name) := s.getType(expr)) {
          return specType(name);
        } else {
          s.report(error(current, "Should be a set type or a type of specication but is %t", expr));
          return unknownType();
        }
      }));
  }
  
  collect(expr, c);
}

void collect(current: (Formula)`<Expr exp> is <QualifiedName state>`, Collector c) {
  c.calculate("is in state", current, [exp],
    AType (Solver s) {
      s.requireTrue(specType(_) := s.getType(exp),  
                    error(current, "Can only perform an \'is\' operation on a specification"));
        
      return boolType();
    });

  c.useViaType(exp, state, {stateId()});

  collect(exp,c);
}

void collect(current: (Formula)`<Expr lhs> in <Expr rhs>`, Collector c) {
  c.calculate("membership", current, [lhs,rhs],
    AType (Solver s) {
      switch(<s.getType(lhs), s.getType(rhs)>) {
        case <AType t, setType(t)>: return boolType();
        default: s.report(error(current, "Can only check membership of element of same type as set"));
      }
    });

  collect(lhs,rhs,c);
}

void collect(current: (Formula)`<Expr lhs> notin <Expr rhs>`, Collector c) {
  c.calculate("non membership", current, [lhs,rhs],
    AType (Solver s) {
      switch(<s.getType(lhs), s.getType(rhs)>) {
        case <AType t, setType(t)>: return boolType();
        default: s.report(error(current, "Can only check membership of element of same type as set"));
      }
    });

  collect(lhs,rhs,c);
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

void collect(current: (Formula)`noOp(<Expr expr>)`, Collector c) {
  c.fact(current, boolType());
  collect(expr, c);
}

void collect(current: (Expr)`(<Expr expr>)`, Collector c) {
  c.fact(current, expr);
  collect(expr, c);
}

void collect(current: (Expr)`- <Expr expr>`, Collector c) {
  c.calculate("sign", current, [expr], 
    AType (Solver s) {
      s.requireEqual(expr, intType(), error(current, "Expression should be of type integer"));
      return intType();
    });
    
  collect(expr, c);
}

void collect(current: (Expr)`|<Expr expr>|`, Collector c) {
  c.calculate("absolute or size", current, [expr], 
    AType (Solver s) {
      AType tipe = s.getType(expr);
      if (intType() !:= tipe, setType(_) !:= tipe) {
        s.report(error(current, "Expression should be a set or integer type"));
      }
      
      return intType();
    });
    
  collect(expr, c);
}

void collect(current: (Expr)`<Expr expr>'`, Collector c) {
  if ([prePhase()] := c.getStack("phase")) {
    c.report(error(current, "Can not reference post value in precondition"));
  }
  
  c.enterScope(current);
    c.fact(current, expr);
    collect(expr, c);
  c.leaveScope(current);
}

void collect(current: (Expr)`<Expr lhs> ++ <Expr rhs>`, Collector c) {
  c.calculate("string concat", current, [lhs, rhs],
    AType (Solver s) {
      if ({stringType()} != {s.getType(lhs), s.getType(rhs)}) {
        s.report(error(current, "++ only works for strings"));
      }
      
      return stringType();
    });  
    
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> + <Expr rhs>`, Collector c) {
  c.calculate("addition", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        case {setType(AType elem), elem}: return setType(elem);
        case {setType(voidType()), AType elem}: return setType(elem);
        case {specType(str name)}: return setType(specType(name));
        default:
          s.report(error(current, "`+` not defined for %t and %t", lhs, rhs));
      }
      
      return intType();
    });  
    
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> - <Expr rhs>`, Collector c) {
  c.calculate("subtraction", current, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        case {setType(AType elem), elem}: return setType(elem);
        default: {
          s.report(error(current, "`-` not defined for %t and %t", lhs, rhs));
          return unknownType();
        }
      }
    });    
  
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> * <Expr rhs>`, Collector c)  = collectIntOp(lhs, rhs, current, "*", "multiplication", c);
void collect(current: (Expr)`<Expr lhs> / <Expr rhs>`, Collector c) = collectIntOp(lhs, rhs, current, "/", "division", c);
void collect(current: (Expr)`<Expr lhs> % <Expr rhs>`, Collector c) = collectIntOp(lhs, rhs, current, "%", "remainder", c);

void collectIntOp(Expr lhs, Expr rhs, Expr complete, str op, str description, Collector c) {
  c.calculate(description, complete, [lhs, rhs],
    AType (Solver s) {
      switch({s.getType(lhs), s.getType(rhs)}){
        case {intType()}: return intType();
        default: {
          s.report(error(complete, "`<op>` not defined for %t and %t", lhs, rhs));
          return unknownType();
        }
      }
    });  
    
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`{<Decl d> | <Formula frm>}`, Collector c) {
  if ((Decl)`<Id var> : <Expr expr>` := d) {
    c.calculate("comprehension", current, [expr], 
      AType (Solver s) {
        return setType(s.getType(expr));
      });
  } else {
    c.report(error(current, "Comprehension only allows a single declaration"));
  }

  c.enterScope(current);
    collectQuant([d], frm, c);
  c.leaveScope(current);
}

void collect(current: (Expr)`<Id var>`, Collector c) {
  c.use(var, {paramId(), quantVarId(), specId(), instanceId()});
}

void collect(current: (Expr)`<Expr expr>.<Id fld>`, Collector c) {
  c.useViaType(expr, fld, {fieldId()});
  c.fact(current, fld);
  
  collect(expr,c);
}

void collect(current: (Expr)`<Id func>(<{Expr ","}* actuals>)`, Collector c) {
  args = [arg | arg <- actuals];
  
  c.calculate("function call <func>", current, args, 
    AType (Solver s) {
      argTypes = atypeList([s.getType(a) | a <- args]); 
      formalTypes = atypeList([]);
      returnType = stringType();
      
      switch("<func>") {
        case "substr": formalTypes = atypeList([stringType(), intType(), intType()]);
        case "toStr": formalTypes = atypeList([intType()]);
        case "toInt": {
          formalTypes = atypeList([stringType()]);
          returnType = intType();
        }
        default: s.report(error(current, "unknown function `<func>`"));
      }
      
      s.requireEqual(argTypes, formalTypes, 
        error(current, "Expected arguments %t, found %t", formalTypes, argTypes));
        
      return returnType; 
    });
  
  collect(actuals,c);
}
 
void collect(current: (Expr)`<Expr spc>[<Id inst>]`, Collector c) {
  c.useViaType(spc, inst, {specInstanceId()});
  c.fact(current, inst);
  
  collect(spc,c);
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

void collect(current: (Lit)`none`, Collector c) {
  c.fact(current, voidType());
}

void collect(current: (Lit)`{<{Expr ","}* elems>}`, Collector c) {
  list[Expr] elements = [e | e <- elems];
  
  if (elements == []) { 
    c.fact(current,  setType(voidType()));
  } else {
    c.calculate("set literal", current, elements, 
      AType (Solver s) {
        AType elemType = s.getType(elements[0]);
        for (e <- elements, s.getType(e) != elemType) {
          s.report(error(current, "Elements in set have different types")); 
        }
        
        return setType(elemType);
      });
  }
  
  collect(elems, c);
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

void collect(current: TypeName tn, Collector c) {
  c.use(tn, {specId()});
}

bool subtype(AType a, a) = true;
bool subtype(setType(voidType()), setType(_)) = true;
bool subtype(setType(_), setType(voidType())) = true;
bool subtype(setType(AType a), setType(AType b)) = subtype(a,b);

bool subtype(voidType(), optionalType(_)) = true;
bool subtype(optionalType(_), voidType()) = true;
bool subtype(optionalType(AType a), a) = true;
bool subtype(AType a, optionalType(a)) = true;
bool subtype(optionalType(AType a), optionalType(AType b)) = subtype(a,b);

bool subtype(specType(str a), specInstanceType(str b)) = a == b;
bool subtype(specInstanceType(str b), specType(str a)) = a == b;

default bool subtype(AType a, AType b) = false; 