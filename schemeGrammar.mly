%{
open Interp
%}
%start expr
%type <Interp.expr> expr
%token Tlparen Trparen Tdot Tapost Lambda
%token <string> Identifier
%token <int> Integer
%%
expr :
   | Identifier { Variable $1 }
   | Integer { IntegerS $1 }
   | Tapost expr { Cons(Variable "quote",$2) }
   | plist { $1 }
plist :
   | Tlparen list Trparen { $2 }
   | Tlparen Trparen { NilS }
list :
   | { NilS }
   | expr Tdot expr { Cons($1,$3) }
   | expr list { Cons($1,$2) }
pnlist :
   | Tlparen nlist Trparen { $2 }
   | Tlparen Trparen { NilS }
nlist :
   | { NilS }
   | expr nlist { Cons($1,$2) }
