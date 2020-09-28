module rebel::lang::CheckSyntax

import rebel::lang::CommonSyntax;
import rebel::lang::SpecSyntax;

syntax Part
  = Config cfg
  | Assert asrt
  | Check chk
  ;
  
syntax Config = "config" Id name "=" {InstanceSetup ","}+ instances ";";

syntax InstanceSetup 
  = {Id ","}+ labels ":" Type spec Abstracts? abstracts Forget? forget InState? inState WithAssignments? assignments
  | Id label WithAssignments assignments
  ;

syntax Abstracts = "abstracts" Type concrete;

syntax Forget = "forget" {Id ","}+ fields;

syntax InState = "is" State state;

syntax WithAssignments = "with" {Assignment ","}+ assignments;

syntax Assignment
  = Id fieldName "=" Expr val
  ;
  
syntax Assert = "assert" Id name "=" Formula form ";";

syntax Formula 
  = non-assoc "if" Formula cond "then" Formula then "else" Formula else
  > TransEvent event "on" Expr var WithAssignments? with
  > "next" Formula form
  | "first" Formula form
  | "last" Formula form
  > "eventually" Formula form
  | "always" Formula form
  | "always-last" Formula form
  | right Formula first "until" Formula second
  | right Formula first "release" Formula second
  ;

syntax TransEvent 
  = wildcard: "*"
  ;

syntax Check 
  = Command cmd Id name "from" Id config "in" SearchDepth depth Objectives? objs Expect? expect";"
  ;

syntax Command
  = "check"
  | "run"
  ;
  
syntax SearchDepth
  = "max" Int steps "steps"
  | "exact" Int steps "steps"
  ;  

syntax Objectives
  = "with" {Objective ","}+ objs
  ;
  
syntax Objective
  = "minimal" Expr expr
  | "maximal" Expr expr
  | "infinite" "trace"
  | "finite" "trace"
  ;

syntax Expect
  = "expect" ExpectResult
  ;
  
syntax ExpectResult
  = "trace"
  | "no" "trace"
  ;  
  
keyword Keywords 
  = "config"
  | "with"
  | "assert"
  | "fact"
  | "until"
  | "release"
  | "eventually"
  | "always"
  | "always-last"
  | "next"
  | "minimal"
  | "maximal"
  | "exact"
  | "on"
  | "first"
  | "last"
  | "inifinite"
  | "finite"
  | "trace"
  | "check"
  | "run"
  ;
