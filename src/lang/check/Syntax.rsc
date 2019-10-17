module lang::check::Syntax

extend lang::std::Layout;

start syntax Module
  = ModuleId module Import* imports Part+ parts
  ;

syntax ModuleId = "module" QualifiedName name; 

syntax Import = "import" QualifiedName module;

syntax QualifiedName = {Id "::"}+ names !>> "::";

syntax Part 
  = Config config
  | Assert assert
  | Check check
  ;

syntax Config = "config" Id name InstanceSetup+ instances;

syntax InstanceSetup = {Id ","}+ labels ":" Id spec InState? inState WithAssignments? assignments;

syntax InState = "in" Id state;

syntax WithAssignments = "with" Assignment+ assignments;

syntax Assert = "assert" Id name "starting" "from" Id config Formula form;

syntax Formula
  = brackets: "(" Formula ")"
  | Expr "is" Id
  | Expr "raised"
  > Expr "\<" Expr
  | Expr "\<=" Expr
  | Expr "=" Expr
  | Expr "!=" Expr
  | Expr "\>=" Expr
  | Expr "\>" Expr
  > right Formula "&&" Formula
  | right Formula "||" Formula
  > right Formula "=\>" Formula
  | right Formula "\<=\>" Formula
  > "forall" Decl+ "|" Formula
  | "exists" Decl+ "|" Formula 
  > "eventually" Formula
  | "always" Formula
  | "next" Formula
  | Formula "until" Formula
  ;
  
syntax Decl = {Id ","}+ labels ":" Expr var;