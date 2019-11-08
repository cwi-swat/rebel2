module rebel::lang::CommonSyntax

extend lang::std::Layout;

start syntax Module
  = ModuleId module Import* imports Part+ parts
  ;

syntax Part = "$$PART$$"; // only here for extention reasons

syntax ModuleId = "module" QualifiedName name; 

syntax Import = "import" QualifiedName module;

syntax QualifiedName = {Id "::"}+ names !>> "::";

syntax Formula
  = brackets: "(" Formula ")"
  > "!" Formula form
  > sync: Expr spc "." Id event  "(" {Expr ","}* params ")" 
  | inState: Expr "is" Id
  | membership: Expr "in" Expr
  | nonMembership: Expr "notin" Expr
  > Expr "\<" Expr
  | Expr "\<=" Expr
  | Expr "=" Expr
  | Expr "!=" Expr
  | Expr "\>=" Expr
  | Expr "\>" Expr
  > "forall" {Decl ","}+ "|" Formula
  | "exists" {Decl ","}+ "|" Formula
  > right Formula "&&" Formula
  | right Formula "||" Formula
  > right Formula "=\>" Formula
  | right Formula "\<=\>" Formula
  | non-assoc "if" Formula cond "then" Formula then "else" Formula else
  ;

syntax Formula
  = noOp: "__noop" "(" Expr spc ")" 
  ;

syntax Decl = {Id ","}+ vars ":" Expr expr;
  
syntax Expr
  = brackets: "(" Expr ")"
  > var: Id
  | fieldAccess: "this" "." Id 
  | Lit
  | "now"
  | "now" "." Id
  > nextVal: Expr "\'"
  > "-" Expr
  > assoc Expr lhs "*" Expr rhs
  | non-assoc Expr lhs "/" Expr rhs
  > assoc Expr lhs "+" Expr rhs
  | non-assoc Expr lhs "-" Expr rhs
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
                 | "now" 
                 | "this" 
                 | "is"
                 | "set"
                 | "forall"
                 | "exists"
                 | "__noop"
                 | "if"
                 | "then"
                 | "else"
                 ;
 