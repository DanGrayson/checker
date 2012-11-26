%{ 

open Typesystem
open Helpers
open Grammar0

%}
%start command unusedtokens ts_exprEof lf_exprEof
%type <Toplevel.command> command
%type <Typesystem.expr> ts_exprEof
%type <Typesystem.expr> lf_exprEof
%type <Typesystem.canonical_type_family> canonical_type_family
%token <int> Nat
%type <unit> unusedtokens
%token <string> IDENTIFIER
%token <Typesystem.var> Var_token 
%token
  Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar
  Warrow Wequalequal Wequal Wturnstile Wtriangle Wcolonequal Wlbrace Wrbrace
  Wbar Wunderscore WF_Print WRule Wgreaterequal Wgreater Wlessequal Wless Wsemi
  KUlevel Kumax KType KPi Klambda KSigma WEl WPi Wev Wu Wj WU Wlambda Wforall
  Kforall WSigma WCoprod WCoprod2 WEmpty Wempty Wempty_r WIC WId WTau WPrint
  WDefine WShow WEnd WVariable WAlpha Weof Watat WCheck WCheckUniverses Wflush
  Prec_application Wdef Flambda

/* precedences, lowest first */
%right
  KPi KSigma
%right
  Warrow
%nonassoc
  Wstar				/* we want [*f x] to be [*(f x)] and [*X->Y] to be [( *X )->Y] */
%left
  Prec_application
%right
  Klambda Kforall
%nonassoc
  Wforall Wunderscore Wplus Wu Wlparen Wlambda Wj Wev Wdef IDENTIFIER Wempty_r
  Wempty WU WSigma WPi WId WIC WEmpty WEl WCoprod2 WCoprod Kumax Watat

%%

canonical_type_family:
| Wlparen t=canonical_type_family Wrparen 
    { t }
| f=canonical_type_family_head args=list(lf_expr)
    { F_APPLY(f,args) }
| KPi v=bare_variable Wcolon a=canonical_type_family Wcomma b=canonical_type_family
    %prec KPi
    { F_Pi(v,a,b) }
| a=canonical_type_family Warrow b=canonical_type_family
   { F_Pi(VarUnused,a,b) }

canonical_type_family_head:
| l=IDENTIFIER 
    { try List.assoc l tfhead_strings with Not_found -> $syntaxerror }

lf_exprEof: a=lf_expr Weof {a}

lf_expr:
| e=bare_lf_expr
  { with_pos (Error.Position($startpos, $endpos)) e  }
| Wlparen Flambda v=variable Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }
| Wlparen Flambda v=variable_unused Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }

variable_unused:
| Wunderscore
    { Error.Position($startpos, $endpos), VarUnused }

bare_lf_expr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| Wlparen f=lf_term_head args=list(lf_expr) Wrparen
    { APPLY(f,args) }

lf_term_head:
| Wlbracket Klambda Wrbracket
    { O O_lambda }
| Wlbracket Kforall Wrbracket
    { O O_forall }
| Wlbracket KPi Wrbracket
    { T T_Pi }
| Wlbracket KSigma Wrbracket
    { T T_Sigma }
| Wlbracket l=IDENTIFIER Wrbracket
    { try List.assoc ("[" ^ l ^ "]") label_strings with Not_found -> $syntaxerror }
| l=IDENTIFIER 
    { V (Var l) }

command: c=command0 
  { Error.Position($startpos, $endpos), c }

command0:
| Weof
    { raise Error.Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KUlevel eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WPrint e=lf_expr Wperiod
    { Toplevel.Print e }
| WF_Print t=canonical_type_family Wperiod
    { Toplevel.F_Print t }
| WCheck o=ts_expr Wperiod
    { Toplevel.Check o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WAlpha e1=ts_expr Wequalequal e2=ts_expr Wperiod
    { Toplevel.Alpha (e1, e2) }
| WTau o=ts_expr Wperiod
    { Toplevel.Type o }

| WRule name=IDENTIFIER Wcolon t=canonical_type_family Wperiod
    { Toplevel.Rule (name,t) }

| WDefine name=IDENTIFIER parms=parmList Wcolonequal t=ts_expr Wperiod 
    { Toplevel.Definition (tDefinition name (fixParmList parms) t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o=ts_expr Wcolon t=ts_expr Wperiod 
    { Toplevel.Definition (oDefinition name (fixParmList parms) o t) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal t1=ts_expr Wequalequal t2=ts_expr Wperiod 
    { Toplevel.Definition (teqDefinition (Ident name,(fixParmList parms,t1,t2))) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o1=ts_expr Wequalequal o2=ts_expr Wcolon t=ts_expr Wperiod 
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
oParm: vars=nonempty_list(IDENTIFIER) Wcolon t=ts_expr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=ts_expr Wequal v=ts_expr 
    { (u,v) }
| v=ts_expr Wgreaterequal u=ts_expr 
    { nowhere (APPLY(U U_max, [ u; v])), v }
| u=ts_expr Wlessequal v=ts_expr 
    { nowhere (APPLY(U U_max, [ u; v])), v }
| v=ts_expr Wgreater u=ts_expr 
    { nowhere (APPLY(U U_max, [ nowhere (APPLY( U (U_plus 1),[u])); v])), v }
| u=ts_expr Wless v=ts_expr 
    { nowhere (APPLY(U U_max, [ nowhere (APPLY( U (U_plus 1),[u])); v])), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

ts_exprEof: a=ts_expr Weof {a}

variable:
| bare_variable
    { Error.Position($startpos, $endpos), $1 }
ts_expr:
| bare_ts_expr
    { with_pos (Error.Position($startpos, $endpos)) $1 }
| parenthesized(ts_expr) 
    {$1}
| Watat e=lf_expr
    {e}
bare_variable:
| IDENTIFIER
    { Var $1 }
bare_ts_expr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| Wu Wlparen u=ts_expr Wrparen
    { make_OO_u u }
| Wj Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { make_OO_j u v }
| Wev x=variable Wrbracket Wlparen f=ts_expr Wcomma o=ts_expr Wcomma t=ts_expr Wrparen
    { make_OO_ev f o (x,t) }
| Wev Wunderscore Wrbracket Wlparen f=ts_expr Wcomma o=ts_expr Wcomma t=ts_expr Wrparen
    { make_OO_ev f o ((Error.Nowhere, VarUnused), t) }
| f=ts_expr o=ts_expr
    %prec Prec_application
    { make_OO_ev f o ((Error.Nowhere, VarUnused), with_pos (Error.Position($startpos, $endpos)) (new_hole'())) }
| Wlambda x=variable Wrbracket Wlparen t=ts_expr Wcomma o=ts_expr Wrparen
    { make_OO_lambda t (x,o) }
| Klambda x=variable Wcolon t=ts_expr Wcomma o=ts_expr
    %prec Klambda
    { make_OO_lambda t (x,o) }
| Wforall x=variable Wrbracket Wlparen u1=ts_expr Wcomma u2=ts_expr Wcomma o1=ts_expr Wcomma o2=ts_expr Wrparen
    { make_OO_forall u1 u2 o1 (x,o2) }
| Kforall x=variable Wcolon Wstar o1=ts_expr Wcomma o2=ts_expr (* not sure about this syntax *)
    %prec Kforall
    { make_OO_forall (new_hole ()) (new_hole ()) o1 (x,o2) }
| Wempty Wlparen Wrparen
    { make_OO_empty }
| Wempty_r Wlparen t=ts_expr Wcomma o=ts_expr Wrparen
    { make_OO_empty_r t o }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,ts_expr) 
    Wrparen { make_Defapp name u [] [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,ts_expr) Wsemi
    t=separated_list(Wcomma,ts_expr) 
    Wrparen { make_Defapp name u t [] }
| Wdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,ts_expr) Wsemi
    t=separated_list(Wcomma,ts_expr) Wsemi
    o=separated_list(Wcomma,ts_expr) 
    Wrparen { make_Defapp name u t o }
| WEl Wlparen o=ts_expr Wrparen
    { make_TT_El o }
| Wstar o=ts_expr
    { make_TT_El o }
| WU Wlparen u=ts_expr Wrparen
    { make_TT_U u }
| WPi x=variable Wrbracket Wlparen t1=ts_expr Wcomma t2=ts_expr Wrparen 
    { make_TT_Pi t1 (x,t2) }
| KPi x=variable Wcolon t1=ts_expr Wcomma t2=ts_expr
    %prec KPi
    { make_TT_Pi t1 (x,t2) }
| t=ts_expr Warrow u=ts_expr
    { make_TT_Pi t ((Error.Nowhere, VarUnused),u) }
| WSigma x=variable Wrbracket Wlparen t1=ts_expr Wcomma t2=ts_expr Wrparen
    { make_TT_Sigma t1 (x,t2) }
| KSigma x=variable Wcolon t1=ts_expr Wcomma t2=ts_expr
    %prec KSigma
    { make_TT_Sigma t1 (x,t2) }
| WCoprod Wlparen t1=ts_expr Wcomma t2=ts_expr Wrparen
    { make_TT_Coprod t1 t2 }
| WCoprod2 x1=variable Wcomma x2=variable Wrbracket Wlparen t1=ts_expr Wcomma t2=ts_expr Wcomma s1=ts_expr Wcomma s2=ts_expr Wcomma o=ts_expr Wrparen
    { make_TT_Coprod2 t1 t2 (x1,s1) (x2,s2) o }
| WEmpty Wlparen Wrparen 
    { make_TT_Empty }
| WIC x=variable Wcomma y=variable Wcomma z=variable Wrbracket
    Wlparen tA=ts_expr Wcomma a=ts_expr Wcomma tB=ts_expr Wcomma tD=ts_expr Wcomma q=ts_expr Wrparen 
    { make_TT_IC tA a (x,tB,(y,tD,(z,q))) }
| WId Wlparen t=ts_expr Wcomma a=ts_expr Wcomma b=ts_expr Wrparen 
    { make_TT_Id t a b }
| u=ts_expr Wplus n=Nat
    { APPLY(U (U_plus n), [u]) }
| Kumax Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { APPLY(U U_max,[u;v])  }
