module rebel::lang::CheckSyntax

import rebel::lang::CommonSyntax;
import rebel::lang::SpecSyntax;

syntax Part
  = Config cfg
  | Assert asrt
  | Check chk
  | Fact fct
  ;
  
syntax Config = "config" Id name "=" {InstanceSetup ","}+ instances ";";

syntax InstanceSetup 
  = {Id ","}+ labels ":" Type spec InState? inState WithAssignments? assignments
  | Id label WithAssignments assignments
  ;

syntax InState = "is" State state;

syntax WithAssignments = "with" {Assignment ","}+ assignments;

syntax Assignment
  = Id fieldName "=" Expr val
  ;

syntax Assert = "assert" Id name "=" Formula form ";";

syntax Fact = "fact" Id name "=" Formula form ";";

syntax Formula 
  = non-assoc "if" Formula cond "then" Formula then "else" Formula else
  > "eventually" Formula form
  | "always" Formula form
  | "next" Formula form
  | "first" Formula form
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
  | "next"
  | "minimal"
  | "maximal"
  | "on"
  | "first"
  | "inifinite"
  | "finite"
  | "trace"
  ;
