%{
open Interp
%}
%start expr
%type <Interp.expr> expr
%token Tlparen Trparen Tdot Tapost
%token <string> Identifier
%%
expr :
   | Identifier { Variable $1 }
   | Tlparen conscell Trparen { $2 }
   | Tlparen Trparen { NilS }
conscell :
   | expr conscell { Cons($1,$2) }
   | expr Tdot expr { Cons($1,$3) }
   | expr { Cons($1,NilS) }
