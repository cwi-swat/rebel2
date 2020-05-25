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
  > "eventually" Formula form
  | "always" Formula form
  | "always-last" Formula form
  | Formula first "until" Formula second
  | "next" Formula form
  | "first" Formula form
  | "last" Formula form
  | TransEvent event "on" Expr var WithAssignments? with
  ;

syntax TransEvent 
  = wildcard: "*"
  ;

syntax Check = "check" Id name "from" Id config "in" SearchDepth depth Objectives? objs ";";
  
syntax SearchDepth
  = "max" Int steps "steps"
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
  
keyword Keywords 
  = "config"
  | "with"
  | "assert"
  | "fact"
  | "eventually"
  | "always"
  | "always-last"
  | "next"
  | "minimal"
  | "maximal"
  | "on"
  | "first"
  | "inifinite"
  | "finite"
  | "trace"
  ;
