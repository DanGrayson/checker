%{
open Interp
%}
%start expr
%type <Interp.expr> expr
%token Tlparen Trparen Tdot Tapost COMMENT
%token IDENTIFIER
%%
expr :
   | IDENTIFIER { Variable "foo" }
   | Tlparen conscell Trparen { $2 }
conscell :
   | expr conscell { Cons($1,$2) }
   | expr Tdot expr { Cons($1,$3) }
