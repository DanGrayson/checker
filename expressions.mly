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
%token Wlparen Wrparen Wsemi Wlbracket Wrbracket Wplus Wcomma Wperiod WPi Wuu
/* keywords: */
%token Wmax WEl WUU
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
| Wlbracket Wuu Wrbracket Wlparen uLevel Wrparen { Uu $5 }
| Wlparen oExpr Wrparen { $2 }
tExpr :
| tVar { Tvariable $1 }
| Wlbracket WEl Wrbracket Wlparen oExpr Wrparen { El $5 }
| Wlbracket WUU Wrbracket Wlparen uLevel Wrparen { ElUU $5 }
| Wlbracket WPi Wsemi oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { ElForall($7,($4,$9)) }
| Wlparen tExpr Wrparen { $2 }
uLevel :
| uVar { Uvariable $1 }
| uLevel Wplus Nat { Uplus ($1, $3) }
| Wlparen uLevel Wrparen { $2 }
| Wmax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
