%{
open Typesystem
%}
%start tExpr oExpr uLevel command derivation
%type <Typesystem.derivation> derivation
%type <Typesystem.tExpr> tExpr
%type <Typesystem.oExpr> oExpr
%type <Typesystem.uLevel> uLevel
%type <Toplevel.command> command

%token <string> Var_token
%token <int> Nat
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequal Wturnstile Wtriangle
%token Kumax KPi Klambda
%token WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2 WEmpty Wempty WIC WId
%token WCheck_u WCheck_t WCheck_o WType WPrint_t WPrint_o WPrint_u WSubst
%token Wflush
%token Prec_application Prec_lambda

/* precedences, lowest first */
%nonassoc Wlparen Wrparen Wlbracket Wrbracket Wcomma Wperiod Wcolon Wstar Wequal Wturnstile Wtriangle
%nonassoc WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2 WEmpty Wempty WIC WId
%right Wplus Wslash Warrow
%right Kumax KPi Klambda
%left Prec_application

%%

command:
| WPrint_t tExpr Wperiod { Toplevel.Print_t $2 }
| WPrint_o oExpr Wperiod { Toplevel.Print_o $2 }
| WPrint_u uLevel Wperiod { Toplevel.Print_u $2 }
| WType oExpr Wperiod { Toplevel.Type $2 }

derivation_list:
| Wlbracket derivation_list_entries Wrbracket { $2 }
| Wlbracket Wrbracket { [] }
derivation_list_entries:
| derivation { [$1] }
| derivation Wcomma derivation_list { $1 :: $3 }
derivation:
| Wlparen Nat Wcomma Wcomma derivation_list Wrparen { inferenceRule($2,RPNone,$5) }

oVar: Var_token { OVar $1 }
tVar: Var_token { TVar $1 }
uVar: Var_token { UVar $1 }

oExpr:
| Wlparen oExpr Wrparen { $2 }
| oVar { Ovariable $1 }
| Wu Wlparen uLevel Wrparen { O_u $3 }
| Wj Wlparen uLevel Wcomma uLevel Wrparen { O_j($3,$5) }
| Wev oVar Wrbracket Wlparen oExpr Wcomma oExpr Wcomma tExpr Wrparen { O_ev($5,$7,($2,$9)) }
| oExpr oExpr %prec Prec_application { O_ev($1,$2,(OVarDummy,Tvariable TVarDummy)) }
| Wlambda oVar Wrbracket Wlparen tExpr Wcomma oExpr Wrparen { O_lambda($5,($2,$7)) }
| Klambda oVar Wcolon tExpr Wcomma oExpr { O_lambda($4,($2,$6)) }
| Wforall oVar Wrbracket Wlparen uLevel Wcomma uLevel Wcomma oExpr Wcomma oExpr Wrparen { O_forall($5,$7,$9,($2,$11)) }
tExpr:
| Wlparen tExpr Wrparen { $2 }
| tVar { Tvariable $1 }
| WEl Wlparen oExpr Wrparen { El $3 }
| Wstar oExpr { El $2 }
| WU Wlparen uLevel Wrparen { T_U $3 }
| WPi oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { Pi($5,($2,$7)) }
| KPi oVar Wcolon tExpr Wcomma tExpr { Pi($4,($2,$6)) }
| tExpr Warrow tExpr { Pi($1,(OVarDummy,$3)) }
| WSigma oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { Sigma($5,($2,$7)) }
| WCoprod Wlparen tExpr Wcomma tExpr Wrparen { T_Coprod($3,$5) }
| WCoprod2 oVar Wcomma oVar Wrbracket Wlparen tExpr Wcomma tExpr Wcomma tExpr Wcomma tExpr Wcomma oExpr Wrparen { T_Coprod2($7,$9,($2,$11),($4,$13),$15) }
| WEmpty Wlparen Wrparen { T_Empty }
| WIC oVar Wcomma oVar Wcomma oVar Wrbracket Wlparen tExpr Wcomma oExpr Wcomma tExpr Wcomma tExpr Wcomma oExpr Wrparen { 
    let x = $2 and y = $4 and z = $6 and tA = $9 and a = $11 and tB = $13 and tD = $15 and q = $17 in
    T_IC(tA,a,(x,tB,(y,tD,(z,q)))) }
| WId Wlparen tExpr Wcomma oExpr Wcomma oExpr Wrparen { Id($3,$5,$7) }
uLevel:
| Wlparen uLevel Wrparen { $2 }
| Nat { Unumeral $1 }
| uVar { Uvariable $1 }
| uLevel Wplus Nat { Uplus ($1, $3) }
| Kumax Wlparen uLevel Wcomma uLevel Wrparen { Umax ($3,$5)  }
