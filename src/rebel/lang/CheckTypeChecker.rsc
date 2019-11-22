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

void collect(current:(Formula)`<Id event> on <Expr spc> <WithAssignments? with>`, Collector c) {
  c.fact(current, boolType());
  
  c.useViaType(spc, event, {eventId()});
  collect(spc, c);
}

void collect(current:(Check)`check <Id assrt> from <Id config> in <SearchDepth depth> <Objectives? objs>;`, Collector c) {
  c.enterScope(current); 
    c.use(assrt, {assertId()});
    c.use(config, {configId()});
  c.leaveScope(current);  
}
