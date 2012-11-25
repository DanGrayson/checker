%{ 

open Typesystem
open Helpers
open Grammar0

%}
%start command unusedtokens ts_exprEof lf_exprEof
%type <Toplevel.command> command
%type <Typesystem.expr> ts_exprEof
%type <Typesystem.expr> lf_exprEof
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

%token Flambda

/* precedences, lowest first */
%right KPi KSigma
%right Warrow
%nonassoc Wstar				/* we want [*f x] to be [*(f x)] and [*X->Y] to be [( *X )->Y] */
%left Prec_application
%right Klambda Kforall
%nonassoc Wforall Wunderscore Wplus Wu Wlparen Wlambda Wj Wev Wdef IDENTIFIER Wempty_r Wempty 
	  WU WSigma WPi WId WIC WEmpty WEl WCoprod2 WCoprod Kumax

%%

lf_exprEof: a=lfexpr Weof {a}

lfexpr:
| e=bare_lfexpr
  { with_pos (Error.Position($startpos, $endpos)) e  }
| Wlparen Flambda v=variable Wcomma body=lfexpr Wrparen
    { LAMBDA(v,body) }

bare_lfexpr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| Wlparen f=lfhead args=list(lfexpr) Wrparen
    { APPLY(f,args) }

lfhead:
| Klambda
    { O O_lambda }
| l=IDENTIFIER 
    {
     try List.assoc l label_strings
     with Not_found -> raise Error.NotImplemented
   }

command: c=command0 
  { Error.Position($startpos, $endpos), c }

command0:
| Weof
    { raise Error.Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KUlevel eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WPrint e=lfexpr Wperiod
    { Toplevel.Print e }
| WCheck o=tsexpr Wperiod
    { Toplevel.Check o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WAlpha e1=tsexpr Wequalequal e2=tsexpr Wperiod
    { Toplevel.Alpha (e1, e2) }
| WTau o=tsexpr Wperiod
    { Toplevel.Type o }

| WDefine name=IDENTIFIER parms=parmList Wcolonequal t=tsexpr Wperiod 
    { Toplevel.Definition (tDefinition name (fixParmList parms) t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o=tsexpr Wcolon t=tsexpr Wperiod 
    { Toplevel.Definition (oDefinition name (fixParmList parms) o t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal t1=tsexpr Wequalequal t2=tsexpr Wperiod 
    { Toplevel.Definition (teqDefinition (Ident name,(fixParmList parms,t1,t2))) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o1=tsexpr Wequalequal o2=tsexpr Wcolon t=tsexpr Wperiod 
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
oParm: vars=nonempty_list(IDENTIFIER) Wcolon t=tsexpr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=tsexpr Wequal v=tsexpr 
    { (u,v) }
| v=tsexpr Wgreaterequal u=tsexpr 
    { nowhere (APPLY(U U_max, [ u; v])), v }
| u=tsexpr Wlessequal v=tsexpr 
    { nowhere (APPLY(U U_max, [ u; v])), v }
| v=tsexpr Wgreater u=tsexpr 
    { nowhere (APPLY(U U_max, [ nowhere (APPLY( U (U_plus 1),[u])); v])), v }
| u=tsexpr Wless v=tsexpr 
    { nowhere (APPLY(U U_max, [ nowhere (APPLY( U (U_plus 1),[u])); v])), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

ts_exprEof: a=tsexpr Weof {a}

variable:
| bare_variable
    { Error.Position($startpos, $endpos), $1 }
tsexpr:
| bare_ts_expr
    { with_pos (Error.Position($startpos, $endpos)) $1 }
| parenthesized(tsexpr) 
    {$1}
bare_variable:
| IDENTIFIER
    { Var $1 }
bare_ts_expr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| Wu Wlparen u=tsexpr Wrparen
    { make_OO_u u }
| Wj Wlparen u=tsexpr Wcomma v=tsexpr Wrparen
    { make_OO_j u v }
| Wev x=variable Wrbracket Wlparen f=tsexpr Wcomma o=tsexpr Wcomma t=tsexpr Wrparen
    { make_OO_ev f o (x,t) }
| Wev Wunderscore Wrbracket Wlparen f=tsexpr Wcomma o=tsexpr Wcomma t=tsexpr Wrparen
    { make_OO_ev f o ((Error.Nowhere, VarUnused), t) }
| f=tsexpr o=tsexpr
    %prec Prec_application
    { make_OO_ev f o ((Error.Nowhere, VarUnused), with_pos (Error.Position($startpos, $endpos)) (new_hole'())) }
| Wlambda x=variable Wrbracket Wlparen t=tsexpr Wcomma o=tsexpr Wrparen
    { make_OO_lambda t (x,o) }
| Klambda x=variable Wcolon t=tsexpr Wcomma o=tsexpr
    %prec Klambda
    { make_OO_lambda t (x,o) }
| Wforall x=variable Wrbracket Wlparen u1=tsexpr Wcomma u2=tsexpr Wcomma o1=tsexpr Wcomma o2=tsexpr Wrparen
    { make_OO_forall u1 u2 o1 (x,o2) }
| Kforall x=variable Wcolon Wstar o1=tsexpr Wcomma o2=tsexpr (* not sure about this syntax *)
    %prec Kforall
    { make_OO_forall (new_hole ()) (new_hole ()) o1 (x,o2) }
| Wempty Wlparen Wrparen
    { make_OO_empty }
| Wempty_r Wlparen t=tsexpr Wcomma o=tsexpr Wrparen
    { make_OO_empty_r t o }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,tsexpr) 
    Wrparen { make_Defapp name u [] [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,tsexpr) Wsemi
    t=separated_list(Wcomma,tsexpr) 
    Wrparen { make_Defapp name u t [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,tsexpr) Wsemi
    t=separated_list(Wcomma,tsexpr) Wsemi
    o=separated_list(Wcomma,tsexpr) 
    Wrparen { make_Defapp name u t o }
| WEl Wlparen o=tsexpr Wrparen
    { make_TT_El o }
| Wstar o=tsexpr
    { make_TT_El o }
| WU Wlparen u=tsexpr Wrparen
    { make_TT_U u }
| WPi x=variable Wrbracket Wlparen t1=tsexpr Wcomma t2=tsexpr Wrparen 
    { make_TT_Pi t1 (x,t2) }
| KPi x=variable Wcolon t1=tsexpr Wcomma t2=tsexpr
    %prec KPi
    { make_TT_Pi t1 (x,t2) }
| t=tsexpr Warrow u=tsexpr
    { make_TT_Pi t ((Error.Nowhere, VarUnused),u) }
| WSigma x=variable Wrbracket Wlparen t1=tsexpr Wcomma t2=tsexpr Wrparen
    { make_TT_Sigma t1 (x,t2) }
| KSigma x=variable Wcolon t1=tsexpr Wcomma t2=tsexpr
    %prec KSigma
    { make_TT_Sigma t1 (x,t2) }
| WCoprod Wlparen t1=tsexpr Wcomma t2=tsexpr Wrparen
    { make_TT_Coprod t1 t2 }
| WCoprod2 x1=variable Wcomma x2=variable Wrbracket Wlparen t1=tsexpr Wcomma t2=tsexpr Wcomma s1=tsexpr Wcomma s2=tsexpr Wcomma o=tsexpr Wrparen
    { make_TT_Coprod2 t1 t2 (x1,s1) (x2,s2) o }
| WEmpty Wlparen Wrparen 
    { make_TT_Empty }
| WIC x=variable Wcomma y=variable Wcomma z=variable Wrbracket
    Wlparen tA=tsexpr Wcomma a=tsexpr Wcomma tB=tsexpr Wcomma tD=tsexpr Wcomma q=tsexpr Wrparen 
    { make_TT_IC tA a (x,tB,(y,tD,(z,q))) }
| WId Wlparen t=tsexpr Wcomma a=tsexpr Wcomma b=tsexpr Wrparen 
    { make_TT_Id t a b }
| u=tsexpr Wplus n=Nat
    { APPLY(U (U_plus n), [u]) }
| Kumax Wlparen u=tsexpr Wcomma v=tsexpr Wrparen
    { APPLY(U U_max,[u;v])  }
