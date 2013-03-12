%{
open Interp
%}
%start expr
%type <Interp.computation> expr
%token Tlparen Trparen Tdot Tapost 
%token <string> Identifier
%token <int> Integer
%%
expr :
   | Identifier { Variable $1 }
   | Integer { Value (IntegerV $1) }
   | Tapost expr { Cons(Variable "quote",$2) }
   | plist { $1 }
plist :
   | Tlparen llist Trparen { $2 }
llist :
   | { Value NilV }
   | expr Tdot expr { Cons($1,$3) }
   | expr llist { Cons($1,$2) }
