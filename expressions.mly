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
%token Wmax WEl WPi Wev Wu Wj WU Wlambda Wforall
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
| Wlparen oExpr Wrparen { $2 }
| oVar { Ovariable $1 }
| Wu Wlparen uLevel Wrparen { Uu $3 }
| Wj Wlparen uLevel Wcomma uLevel Wrparen { Jj($3,$5) }
| Wev Wsemi oVar Wrbracket Wlparen oExpr Wcomma oExpr Wcomma tExpr Wrparen { Ev($6,$8,($3,$10)) }
| Wlambda Wsemi oVar Wrbracket Wlparen tExpr Wcomma oExpr Wrparen { Lambda($6,($3,$8)) }
| Wforall Wsemi oVar Wrbracket Wlparen uLevel Wcomma uLevel Wcomma oExpr Wcomma oExpr Wrparen { Forall($6,$8,$10,($3,$12)) }
tExpr :
| Wlparen tExpr Wrparen { $2 }
| tVar { Tvariable $1 }
| WEl Wlparen oExpr Wrparen { El $3 }
| WU Wlparen uLevel Wrparen { ElUU $3 }
| WPi Wsemi oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { ElForall($6,($3,$8)) }
uLevel :
| Wlparen uLevel Wrparen { $2 }
| uVar { Uvariable $1 }
| uLevel Wplus Nat { Uplus ($1, $3) }
| Wmax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
