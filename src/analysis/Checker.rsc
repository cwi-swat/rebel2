module analysis::Checker

import lang::Syntax;

extend analysis::typepal::TypePal;

data AType
  = intType(AMult mult)
  | dateType()
  | boolType()
  | specType(AMult mult, str spec)
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
  
str prettyAType(intType(AMult mult)) = "<prettyAMult(mult)> Integer";
str prettyAType(dateType()) = "Date";  
str prettyAType(boolType()) = "Boolean";
str prettyAType(specType(AMult mult, str spec)) = "<prettyAMult(mult)> <spec>";

str prettyAMult(oneMult()) = "one";
str prettyAMult(loneMult()) = "lone";
str prettyAMult(setMult()) = "set";

data ScopeRole
  = specScope()
  | eventScope()
  ;
  
data IdRole
  = eventId()
  | stateId()
  | fieldId()
  | paramId()
  ; 
    
data EventInfo
  = initialEvent()
  ;    
    
void collect(current: (Spec)`<QualifiedName? path> <Import* imports> spec <Id name> <Fields? fields> <Constraints? constraints> <Event* events> <States? states>`, Collector c) { 
  c.enterScope(current); 
    
    if (/Fields flds <- fields) {
      collect(flds.fields, c);
    }  
    
    collect(events, c);
    if (/States sts <- states) {
      collect(sts.trans, c);
    }
  
  c.leaveScope(current);
}  

void collect(current: (Field)`<Id name> : <Type tipe>`, Collector c) {
  c.define("<name>", fieldId(), name, defType(tipe));
  collect(tipe, c);
}

void collect(current: (Transition)`<State from>-\><State to> : <{TransEvent ","}+ events>;`, Collector c) {
  throw "TODO!";
}

void collect(current: (Event)`<Initial? init> event <Id name>(<{FormalParam ","}* params>) <EventBody body>`, Collector c) {
  c.fact(current, boolType());
  
  c.enterScope(current);
    
    if (/(Initial)`init` := init) {
      c.setScopeInfo(c.getScope(), eventScope(), initialEvent());
    }
      
    for (FormalParam p <- params) {
      collect(p, c);
    }   
    
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
  
  //collect(variants, c);
}

//syntax Formula
//  > sync: Expr event  "(" {Expr ","}* params ")"  
//  | Expr "is" State
//  > right Formula "&&" Formula
//  | right Formula "||" Formula
//  > right Formula "=\>" Formula
//  | right Formula "\<=\>" Formula
//  | Expr "\<" Expr
//  | Expr "\<=" Expr
//  | Expr "!=" Expr
//  | Expr "\>=" Expr
//  | Expr "\>" Expr
//  ;

void collect(current: (Formula)`( <Formula f> )`, Collector c) {
  c.fact(current, f);
  collect(f, c);
}

void collect(current: (Formula)`<Expr lhs> = <Expr rhs>`, Collector c) {
  c.calculate("equality", current, [lhs,rhs], 
    AType (Solver s) {
      s.requireEqual(lhs, rhs, error(current, "Equal types required, found %t and %t", lhs, rhs));
      return boolType();
    });
  
  collect(lhs, rhs, c);
}

void collect(current: (Formula)`<Expr lhs> \> <Expr rhs>`, Collector c) {
  c.calculate("gt", current, [lhs,rhs], 
    AType (Solver s) {
      s.requireEqual(lhs, rhs, error(current, "Equal types required, found %t and %t", lhs, rhs));
      return boolType();
    });
  
  collect(lhs, rhs, c);
}

//syntax Expr
//  = brackets: "(" Expr ")"
//  | "this"
//  | "now"
//  > "-" Expr
//  > right Expr lhs "*" Expr rhs
//  | right Expr lhs "\\" Expr rhs
//  > right Expr lhs "+" Expr rhs
//  | right Expr lhs "-" Expr rhs 
//  ; 

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
      switch(<s.getType(lhs), s.getType(rhs)>){
        case <intType(oneMult()), intType(oneMult())>: return intType(oneMult());
        default:
          s.report(error(current, "`+` not defined for %t and %t", lhs, rhs));
      }
    });
  
  collect(lhs, rhs, c);
}

void collect(current: (Expr)`<Expr lhs> - <Expr rhs>`, Collector c) {
  c.calculate("subtraction", current, [lhs, rhs],
    AType (Solver s) {
      switch(<s.getType(lhs), s.getType(rhs)>){
        case <intType(oneMult()), intType(oneMult())>: return intType(oneMult());
        default:
          s.report(error(current, "`-` not defined for %t and %t", lhs, rhs));
      }
    });
  
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

default void collect(current: TypeName tn, Collector c) {
  c.fact(current, specType(c.pop("mult"), "<t>"));
}


