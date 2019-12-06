module rebel::lang::CheckTypeChecker

import rebel::lang::CommonSyntax;
import rebel::lang::SpecSyntax;
import rebel::lang::CheckSyntax;

import util::PathUtil;

extend analysis::typepal::TypePal;

import IO;
 
data AType
  = configType()
  | assertType()
  | factType()
  | checkType()
  ;

data IdRole
  = configId()
  | assertId()
  | factId()
  | checkId()
  ;

void collect(current: (Part)`<Config cfg>`, Collector c) {
  collect(cfg, c);
}  

void collect(current: (Part)`<Assert a>`, Collector c) {
  collect(a, c);
}  

void collect(current: (Part)`<Fact fct>`, Collector c) {
  collect(fct, c);
}  

void collect(current: (Part)`<Check chk>`, Collector c) {
  collect(chk, c);
}  

void collect(current: (Config)`config <Id name> = <{InstanceSetup ","}+ instances>;`, Collector c) {
  c.define("<name>", configId(), current, defType(configType()));
  
  c.enterScope(current); 
    collect(instances, c);
  c.leaveScope(current);  
}

void collect(current: (InstanceSetup)`<{Id ","}+ labels>: <Type spc> <InState? inState> <WithAssignments? assignments>`, Collector c) {
  for (l <- labels) {
    c.define("<l>", instanceId(), l, defType(spc));
  }
  
  if (/(InState)`is <State st>` := inState) {
    c.useViaType(spc, st, {stateId()});
  }
  
  for (/assign:(Assignment)`<Id fieldName> = <Lit val>` := assignments) {
    c.useViaType(spc, fieldName, {fieldId()});
    
    c.requireEqual(fieldName, val, error(assign, "Field is of type %t, but assigned value is of type %t", fieldName, val)); 
    collect(val, c);    
  }
  
  collect(spc, c); 
}

void collect(current: (InstanceSetup)`<Id label> <WithAssignments assignments>`, Collector c) {
  c.use(label, {instanceId()});
  
  for (/assign:(Assignment)`<Id fieldName> = <Lit val>` := assignments) {
    c.useViaType(label, fieldName, {fieldId()});
    c.requireEqual(fieldName, val, error(assign, "Field is of type %t, but assigned value is of type %t", fieldName, val)); 
          
    collect(val, c);
  }  
}

void collect(current:(Assert)`assert <Id name> = <Formula form>;`, Collector c) {
  c.define("<name>", assertId(), current, defType(assertType()));
  
  c.enterScope(current); 
    collect(form, c);
  c.leaveScope(current);    
}

void collect(current:(Fact)`fact <Id name> = <Formula form>;`, Collector c) {
  c.define("<name>", factId(), current, defType(factType()));
  
  c.enterScope(current); 
    collect(form, c);
  c.leaveScope(current);    
}

void collect(current:(Formula)`eventually <Formula form>`, Collector c) {
  c.fact(current, boolType());
  collect(form, c);  
}

void collect(current:(Formula)`always <Formula form>`, Collector c) {
  c.fact(current, boolType());
  collect(form, c);  
}

void collect(current:(Formula)`next <Formula form>`, Collector c) {
  c.fact(current, boolType());
  collect(form, c);  
}

void collect(current:(Formula)`first <Formula form>`, Collector c) {
  c.fact(current, boolType());
  collect(form, c);  
}

void collect(current:(Formula)`<TransEvent event> on <Expr spc> <WithAssignments? w>`, Collector c) {
  c.fact(current, boolType());

  if ((TransEvent)`*` !:= event) {   
    c.useViaType(spc, event, {eventId()});    
  }
  
  if (/WithAssignments wa := w) {
    map[str,Expr] namedArgs = ();
    for (/(Assignment)`<Id name> = <Expr val>` <- wa.assignments) {
      namedArgs["<name>"] = val;
      //c.useViaType(event, name, {paramId()});
    }  
    
    c.calculate("check for raised event <event>", current, event + [namedArgs[n] | n <- namedArgs], 
      AType (Solver s) {
        eType = s.getType(event);
        
        if (eventType(namedTypeList(ntl)) := s.getType(event)) {
          map[str,AType] namedFormals = (name : tipe | <str name, AType tipe> <- ntl); 
          map[str,AType] namedArgs = (n : s.getType(namedArgs[n]) | n <- namedArgs);
                  
          s.requireTrue(namedArgs - namedFormals == (), 
            error(current, "Expected arguments %t, found %t", namedTypeList([<n,namedFormals[n]> | n <- namedFormals]), namedTypeList([<n,namedArgs[n]> | n <- namedArgs]))); 
        } else {
          s.report(error(current, "Event expected, found %t", eType));
        }
        
        return boolType();
      });
  }
    
  //c.push("event", event);
  collect(spc, w, c);
  //c.pop("event");      
}

void collect(current:(WithAssignments)`with <{Assignment ","}+ assignments>`, Collector c) {
  collect(assignments,c);
}

void collect(current:(Assignment)`<Id name> = <Expr val>`, Collector c) {
  //event = c.top("event");
  //println(event);
  //c.useViaType(event, name, {paramId()});
  c.fact(name, val);
  
  collect(val,c);
}

void collect(current:(Check)`check <Id assrt> from <Id config> in <SearchDepth depth> <Objectives? objs>;`, Collector c) {
  c.enterScope(current); 
    c.use(assrt, {assertId()});
    c.use(config, {configId()});
  c.leaveScope(current);  
}
