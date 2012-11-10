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
%token Wlparen Wrparen Wsemi Wlbracket Wrbracket Wplus Wcomma Wperiod
/* keywords: */
%token Wmax
%token <string> OVar			/* starts with lower case */
%token <string> TVar			/* starts with upper case but not with UU */
%token <string> UVar			/* starts with UU */
%token <int> Nat
%%

expr : 
| tExpr Wperiod { Texpr $1 }
| oExpr Wperiod { Oexpr $1 }
| uLevel Wperiod { ULevel $1 }

oVar : OVar { OVar $1 }
tVar : TVar { TVar $1 }
uVar : UVar { UVar $1 }

oExpr :
| oVar { Ovariable $1 }
| Wlparen oExpr Wrparen { $2 }
tExpr :
| tVar { Tvariable $1 }
| Wlparen tExpr Wrparen { $2 }
uLevel :
| uVar { Uvariable $1 }
| uLevel Wplus Nat { Uplus ($1, $3) }
| Wlparen uLevel Wrparen { $2 }
| Wmax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
