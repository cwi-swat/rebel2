module lang::Syntax

extend lang::std::Layout;

start syntax Module
  = ModuleId module Import* imports Part+ parts
  ;

syntax ModuleId = "module" QualifiedName name; 

syntax Import = "import" QualifiedName module;

syntax QualifiedName = {Id "::"}+ names !>> "::";

syntax Part 
  = Spec spc
  ;

syntax Spec = "spec" Id name Fields? fields Constraints? constraints Event* events States? states;

syntax Fields
  = {Field ","}+ fields ";"
  ;

syntax Field
  = Id name ":" Type tipe
  ;
  
syntax Constraints
  = {Constraint ","}+ constraints ";"
  ;
  
syntax Constraint
  = "identity" Id field
  | "identity" "(" {Id ","}+ fields ")"
  ;
  
syntax Event
  = Initial? "event" Id name "(" {FormalParam ","}* params ")" EventBody body 
  ;

syntax Initial
  = "init";
  
syntax FormalParam
  = Id name ":" Type tipe
  ;
  
syntax EventBody
  = Pre? pre Post? post EventVariant* variants
  ;
    
syntax Pre
  = "pre" ":" {Formula ","}* formulas ";"
  ;

syntax Post
  = "post" ":" {Formula ","}* formulas ";"
  ;

syntax EventVariant
  = Outcome outcome Id name EventVariantBody body
  ;  

syntax Outcome
  = "success"
  | "failure"
  ;

syntax EventVariantBody
  = Pre? pre Post? post
  ;  
  
syntax Formula
  = brackets: "(" Formula ")"
  > sync: Expr spc "." Id event  "(" {Expr ","}* params ")"  
  | Expr "is" Id
  > right Formula "&&" Formula
  | right Formula "||" Formula
  > right Formula "=\>" Formula
  | right Formula "\<=\>" Formula
  | Expr "\<" Expr
  | Expr "\<=" Expr
  | Expr "=" Expr
  | Expr "!=" Expr
  | Expr "\>=" Expr
  | Expr "\>" Expr
  ;
  
syntax Expr
  = brackets: "(" Expr ")"
  > var: Id
  | fieldAccess: "this" "." Id 
  | Lit
  | "now"
  | "now" "." Id
  > nextVal: Expr "\'"
  > "-" Expr
  > right Expr lhs "*" Expr rhs
  | right Expr lhs "\\" Expr rhs
  > right Expr lhs "+" Expr rhs
  | right Expr lhs "-" Expr rhs 
  ; 
  
syntax States
  = "states" ":" Transition* trans
  ;
  
syntax Transition
  = State from "-\>" State to ":" {TransEvent ","}+ events ";"
  | State super InnerStates? inner "{" Transition* trans "}"
  ;

syntax InnerStates
  = "[" {State ","}+ states "]"
  ;
  
syntax State
  = Id name
  | "(*)"
  ;
  
syntax TransEvent
  = Id event \ "empty"
  | Id event "::" Id variant
  | "empty"
  ;  
  
syntax Lit
  = Int
  | StringConstant
  | emptySet: "{}" 
  ;

syntax Type
  = TypeName tp
  | "set" TypeName elem
  | "?" TypeName elem
  ;  
  
//syntax Multiplicity
//  = "one"
//  | "lone"
//  | "set"
//  ;
  
lexical Id = [a-z A-Z 0-9 _] !<< ([a-z A-Z_][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Keywords;
lexical TypeName = @category="Type" [a-z A-Z 0-9 _] !<< [A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _] \ Keywords;
lexical Int = @category="Constant"  [0-9] !<< [0-9]+ !>> [0-9];
lexical StringConstant = @category="Constant"  "\"" StringCharacter* "\""; 

lexical StringCharacter
  = "\\" [\" \' \< \> \\ b f n r t] 
  | UnicodeEscape 
  | ![\" \' \< \> \\]
  | [\n][\ \t \u00A0 \u1680 \u2000-\u200A \u202F \u205F \u3000]* [\'] // margin 
  ;
  
lexical UnicodeEscape
  = utf16: "\\" [u] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] 
  | utf32: "\\" [U] (("0" [0-9 A-F a-f]) | "10") [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] [0-9 A-F a-f] // 24 bits 
  | ascii: "\\" [a] [0-7] [0-9A-Fa-f]
  ;
      
keyword Keywords = "module"
                 | "spec"
                 | "now" 
                 | "this" 
                 | "failure" 
                 | "success" 
                 | "identity" 
                 | "unique" 
                 | "event" 
                 | "pre" 
                 | "post"
                 | "is"
                 | "one"
                 | "lone"
                 | "set"
                 | "init"
                 ;
 