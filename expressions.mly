%{
open Typesystem
%}
%start expr
%type <Typesystem.expr> expr
%type <Typesystem.tExpr> tExpr
%type <Typesystem.oExpr> oExpr
%type <Typesystem.uLevel> uLevel
%type <Typesystem.oVar> oVar
%type <Typesystem.tVar> tVar
%type <Typesystem.uVar> uVar
/* punctuation: */
%token Wlparen Wrparen Wsemi Wlbracket Wrbracket Wplus Wcomma
/* keywords: */
%token Wmax
%token <string> OVar			/* starts with lower case */
%token <string> TVar			/* starts with upper case but not with UU */
%token <string> UVar			/* starts with UU */
%token <int> Integer
%%

expr : 
| tExpr { Texpr $1 }
| oExpr { Oexpr $1 }
| uLevel { ULevel $1 }

oVar : OVar { OVar $1 }
tVar : TVar { TVar $1 }
uVar : UVar { UVar $1 }

oExpr :
| oVar { Ovariable $1 }
tExpr :
| tVar { Tvariable $1 }
uLevel :
| uVar { Uvariable $1 }
| uLevel Wplus Integer { Uplus ($1, $3) }
| Wmax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
