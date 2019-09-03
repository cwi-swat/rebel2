module lang::Syntax

extend lang::std::Layout;

//start syntax Module = "module" QualifiedName Import* imports;

start syntax Spec 
  = Import* imports "spec" Id name Fields? fields Constraints? constraints Event* events States? states
  ;
  
syntax Import = "import" QualifiedName module;

syntax QualifiedName = {Id "::"}+ names !>> "::";

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
  = "init"? "event" Id name "(" {FormalParam ","}* params ")" EventBody body 
  ;
  
syntax FormalParam
  = Id name ":" Type tipe
  ;
  
syntax EventBody
  = Pre? pre Post? post Sync? sync EventVariant* variants
  ;
  
syntax Pre
  = "pre" ":" {Formula ","}* formulas ";"
  ;

syntax Post
  = "post" ":" {Formula ","}* formulas ";"
  ;

syntax Sync
  = "sync" ":" {Expr ","}* exprs ";"
  ;

syntax EventVariant
  = ("success" | "failure") Id name EventVariantBody body
  ;

syntax EventVariantBody
  = Pre pre Post? post
  ;
  
syntax Formula
  = brackets: "(" Formula ")"
  > sync: Expr event  "(" {Expr ","}* params ")"  
  | Expr "in" Expr
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
  | fieldAccess: Expr "." Id 
  | Lit
  | "this"
  | "now"
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
  = Id event 
  | Id event "::" {Id "::"}+ variant
  ;  
  
syntax Lit
  = Int
  | StringConstant 
  ;
lexical Id = [a-z A-Z 0-9 _] !<< ([a-z A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _]) \ Keywords;
lexical Type = @category="Type" [a-z A-Z 0-9 _] !<< [A-Z][a-z A-Z 0-9 _]* !>> [a-z A-Z 0-9 _] \ Keywords;
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
      
keyword Keywords = "now" 
                 | "this" 
                 | "failure" 
                 | "success" 
                 | "identity" 
                 | "unique" 
                 | "event" 
                 | "pre" 
                 | "post"
                 | "in"
                 ;
 