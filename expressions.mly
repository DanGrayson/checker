%{
open Typesystem
%}
%start expr command
%type <Typesystem.expr> expr
%type <Toplevel.command> command

/* punctuation: */
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash
/* keywords: */
%token Wmax WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2
/* commands: */
%token WCheck WType WPrint WSubst
/* error recovery tokens */
%token Wflush

%token <string> UVar			/* starts with uu */
%token <string> OVar			/* starts with lower case but not with uu */
%token <string> TVar			/* starts with upper case */
%token <int> Nat
%%

command :
| WCheck expr Wperiod { Toplevel.Check $2 }
| WPrint expr Wperiod { Toplevel.Print $2 }
| WType oExpr Wperiod { Toplevel.Type $2 }
| WSubst expr Wlbracket oExpr Wslash oVar Wrbracket Wperiod { Toplevel.Subst ($2, $4, $6) }

expr : 
| tExpr { Texpr $1 }
| oExpr { Oexpr $1 }
| uLevel { ULevel $1 }

oVar : OVar { OVar $1 }
tVar : TVar { TVar $1 }
uVar : UVar { UVar $1 }

oExpr :
| Wlparen oExpr Wrparen { $2 }
| oVar { Ovariable $1 }
| Wu Wlparen uLevel Wrparen { Uu $3 }
| Wj Wlparen uLevel Wcomma uLevel Wrparen { Jj($3,$5) }
| Wev oVar Wrbracket Wlparen oExpr Wcomma oExpr Wcomma tExpr Wrparen { Ev($5,$7,($2,$9)) }
| Wlambda oVar Wrbracket Wlparen tExpr Wcomma oExpr Wrparen { Lambda($5,($2,$7)) }
| Wforall oVar Wrbracket Wlparen uLevel Wcomma uLevel Wcomma oExpr Wcomma oExpr Wrparen { Forall($5,$7,$9,($2,$11)) }
tExpr :
| Wlparen tExpr Wrparen { $2 }
| tVar { Tvariable $1 }
| WEl Wlparen oExpr Wrparen { El $3 }
| WU Wlparen uLevel Wrparen { UU $3 }
| WPi oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { Pi($5,($2,$7)) }
| WSigma oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { Sigma($5,($2,$7)) }
| WCoprod Wlparen tExpr Wcomma tExpr Wrparen { ElCoprod($3,$5) }
| WCoprod2 oVar Wcomma oVar Wrbracket Wlparen tExpr Wcomma tExpr Wcomma tExpr Wcomma tExpr Wcomma oExpr Wrparen { ElCoprod2($7,$9,($2,$11),($4,$13),$15) }
uLevel :
| Wlparen uLevel Wrparen { $2 }
| uVar { Uvariable $1 }
| uLevel Wplus Nat { Uplus ($1, $3) }
| Wmax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
