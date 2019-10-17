module rebel::lang::SpecSyntax

extend rebel::lang::CommonSyntax;

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
 
keyword Keywords = "spec"
                 | "failure" 
                 | "success" 
                 | "event" 
                 | "pre" 
                 | "post"
                 | "init"
                 | "states"
                 ;
 