%{ 

open Typesystem
open Helpers
open Grammar0

%}
%start command unusedtokens exprEof
%type <Toplevel.command> command
%type <Typesystem.expr> exprEof
%token <int> Nat
%type <unit> unusedtokens
%token <string> IDENTIFIER
%token <Typesystem.var> Var_token 
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequalequal Wequal Wturnstile Wtriangle Wcolonequal
%token Wlbrace Wrbrace Wbar Wunderscore
%token Wgreaterequal Wgreater Wlessequal Wless Wsemi
%token KUlevel Kumax KType KPi Klambda KSigma
%token WEl WPi Wev Wu Wj WU Wlambda Wforall Kforall WSigma WCoprod WCoprod2 WEmpty Wempty Wempty_r WIC WId
%token WTau WPrint WDefine WShow WEnd WVariable WAlpha Weof
%token WCheck WCheckUniverses
%token Wflush
%token Prec_application
%token Wdef

/* precedences, lowest first */
%right KPi KSigma
%right Warrow
%nonassoc Wstar				/* we want [*f x] to be [*(f x)] and [*X->Y] to be [( *X )->Y] */
%left Prec_application
%right Klambda Kforall
%nonassoc Wforall Wunderscore Wplus Wu Wlparen Wlambda Wj Wev Wdef IDENTIFIER Wempty_r Wempty 
	  WU WSigma WPi WId WIC WEmpty WEl WCoprod2 WCoprod Kumax

%%

exprEof: a=expr Weof {a}

command: c=command0 
  { Error.Position($startpos, $endpos), c }

command0:
| Weof
    { raise Error.Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KUlevel eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WPrint e=expr Wperiod
    { Toplevel.Print e }
| WCheck o=expr Wperiod
    { Toplevel.Check o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WAlpha e1=expr Wequalequal e2=expr Wperiod
    { Toplevel.Alpha (e1, e2) }
| WTau o=expr Wperiod
    { Toplevel.Type o }

| WDefine name=IDENTIFIER parms=parmList Wcolonequal t=expr Wperiod 
    { Toplevel.Definition (tDefinition name (fixParmList parms) t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o=expr Wcolon t=expr Wperiod 
    { Toplevel.Definition (oDefinition name (fixParmList parms) o t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal t1=expr Wequalequal t2=expr Wperiod 
    { Toplevel.Definition (teqDefinition (Ident name,(fixParmList parms,t1,t2))) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o1=expr Wequalequal o2=expr Wcolon t=expr Wperiod 
    { Toplevel.Definition (oeqDefinition (Ident name,(fixParmList parms,o1,o2,t))) }

| WShow Wperiod 
    { Toplevel.Show }
| WEnd Wperiod
    { Toplevel.End }

unusedtokens: 
    Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile Wempty
    Wempty_r Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile
    Wlbracket Wbar Var_token Wplus
    { () }

uParm: vars=nonempty_list(IDENTIFIER) Wcolon KUlevel eqns=preceded(Wsemi,uEquation)*
    { UParm (UContext ((List.map make_Var vars),eqns)) }
tParm: vars=nonempty_list(IDENTIFIER) Wcolon KType 
    { TParm (List.map make_Var vars) }
oParm: vars=nonempty_list(IDENTIFIER) Wcolon t=expr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=expr Wequal v=expr 
    { (u,v) }
| v=expr Wgreaterequal u=expr 
    { nowhere (APPLY(UU UU_max, [ u; v])), v }
| u=expr Wlessequal v=expr 
    { nowhere (APPLY(UU UU_max, [ u; v])), v }
| v=expr Wgreater u=expr 
    { nowhere (APPLY(UU UU_max, [ nowhere (APPLY( UU (UU_plus 1),[u])); v])), v }
| u=expr Wless v=expr 
    { nowhere (APPLY(UU UU_max, [ nowhere (APPLY( UU (UU_plus 1),[u])); v])), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

variable:
| bare_variable
    { Error.Position($startpos, $endpos), $1 }
expr:
| bare_expr
    { with_pos (Error.Position($startpos, $endpos)) $1 }
| parenthesized(expr) 
    {$1}
bare_variable:
| IDENTIFIER
    { Var $1 }
bare_expr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| Wu Wlparen u=expr Wrparen
    { make_OO_u u }
| Wj Wlparen u=expr Wcomma v=expr Wrparen
    { make_OO_j u v }
| Wev x=variable Wrbracket Wlparen f=expr Wcomma o=expr Wcomma t=expr Wrparen
    { make_OO_ev f o (x,t) }
| Wev Wunderscore Wrbracket Wlparen f=expr Wcomma o=expr Wcomma t=expr Wrparen
    { make_OO_ev f o ((Error.Nowhere, VarUnused), t) }
| f=expr o=expr
    %prec Prec_application
    { make_OO_ev_hole f o }
| Wlambda x=variable Wrbracket Wlparen t=expr Wcomma o=expr Wrparen
    { make_OO_lambda t (x,o) }
| Klambda x=variable Wcolon t=expr Wcomma o=expr
    %prec Klambda
    { make_OO_lambda t (x,o) }
| Wforall x=variable Wrbracket Wlparen u1=expr Wcomma u2=expr Wcomma o1=expr Wcomma o2=expr Wrparen
    { make_OO_forall u1 u2 o1 (x,o2) }
| Kforall x=variable Wcolon Wstar o1=expr Wcomma o2=expr (* not sure about this syntax *)
    %prec Kforall
    { make_OO_forall (new_hole ()) (new_hole ()) o1 (x,o2) }
| Wempty Wlparen Wrparen
    { make_OO_empty }
| Wempty_r Wlparen t=expr Wcomma o=expr Wrparen
    { make_OO_empty_r t o }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,expr) 
    Wrparen { make_Defapp name u [] [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,expr) Wsemi
    t=separated_list(Wcomma,expr) 
    Wrparen { make_Defapp name u t [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,expr) Wsemi
    t=separated_list(Wcomma,expr) Wsemi
    o=separated_list(Wcomma,expr) 
    Wrparen { make_Defapp name u t o }
| WEl Wlparen o=expr Wrparen
    { make_TT_El o }
| Wstar o=expr
    { make_TT_El o }
| WU Wlparen u=expr Wrparen
    { make_TT_U u }
| WPi x=variable Wrbracket Wlparen t1=expr Wcomma t2=expr Wrparen 
    { make_TT_Pi t1 (x,t2) }
| KPi x=variable Wcolon t1=expr Wcomma t2=expr
    %prec KPi
    { make_TT_Pi t1 (x,t2) }
| t=expr Warrow u=expr
    { make_TT_Pi t ((Error.Nowhere, VarUnused),u) }
| WSigma x=variable Wrbracket Wlparen t1=expr Wcomma t2=expr Wrparen
    { make_TT_Sigma t1 (x,t2) }
| KSigma x=variable Wcolon t1=expr Wcomma t2=expr
    %prec KSigma
    { make_TT_Sigma t1 (x,t2) }
| WCoprod Wlparen t1=expr Wcomma t2=expr Wrparen
    { make_TT_Coprod t1 t2 }
| WCoprod2 x1=variable Wcomma x2=variable Wrbracket Wlparen t1=expr Wcomma t2=expr Wcomma s1=expr Wcomma s2=expr Wcomma o=expr Wrparen
    { make_TT_Coprod2 t1 t2 (x1,s1) (x2,s2) o }
| WEmpty Wlparen Wrparen 
    { make_TT_Empty }
| WIC x=variable Wcomma y=variable Wcomma z=variable Wrbracket
    Wlparen tA=expr Wcomma a=expr Wcomma tB=expr Wcomma tD=expr Wcomma q=expr Wrparen 
    { make_TT_IC tA a (x,tB,(y,tD,(z,q))) }
| WId Wlparen t=expr Wcomma a=expr Wcomma b=expr Wrparen 
    { make_TT_Id t a b }
| u=expr Wplus n=Nat
    { APPLY(UU (UU_plus n), [u]) }
| Kumax Wlparen u=expr Wcomma v=expr Wrparen
    { APPLY(UU UU_max,[u;v])  }
