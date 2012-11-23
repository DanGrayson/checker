%{ 

open Typesystem

type parm =
  | UParm of uContext
  | TParm of tContext
  | OParm of oContext

let fixParmList (p:parm list) : uContext * tContext * oContext = (* this code has to be moved somewhere to use the context *)
  let rec fix us ts os p =
    match p with 
    | UParm u :: p -> 
	if List.length ts > 0 or List.length os > 0 then raise (Error.GeneralError "expected universe-level variables first");
	fix (u::us) ts os p
    | TParm t :: p -> 
	if List.length os > 0 then raise (Error.Unimplemented "a type parameter after an object parameter");
	fix us (t::ts) os p
    | OParm o :: p -> fix us ts (o::os) p
    | [] -> ( 
	let tc = List.flatten (List.rev_append ts [])
	and oc = List.flatten (List.rev_append os [])
	and uc = match (List.rev_append us []) with
	| [] -> emptyUContext
	| (uc :: []) -> uc
	| _ -> raise (Error.Unimplemented "merging of universe level variable lists")
	in (uc,tc,oc))
  in fix [] [] [] p

%}
%start command unusedtokens tExprEof oExprEof
%type <Toplevel.command> command
%type <Typesystem.expr> tExprEof
%type <Typesystem.expr> oExprEof
%token <int> Nat
%type <unit> unusedtokens
%token <string> IDENTIFIER
%token <Typesystem.var> Var_token 
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequalequal Wequal Wturnstile Wtriangle Wcolonequal
%token Wlbrace Wrbrace Wbar Wunderscore
%token Wgreaterequal Wgreater Wlessequal Wless Wsemi
%token KUlevel Kumax KType KPi Klambda KSigma Kulevel
%token WEl WPi Wev Wu Wj WU Wlambda Wforall Kforall WSigma WCoprod WCoprod2 WEmpty Wempty Wempty_r WIC WId
%token WTau WPrint WDefine Wtype Wequality WShow WEnd WVariable WoAlpha WtAlpha WuAlpha Weof
%token WCheck WCheckUniverses
%token Wflush
%token Prec_application
%token Wtdef Wodef

/* precedences, lowest first */
%right KPi KSigma
%right Warrow
%left Prec_application
%right Klambda Kforall
%nonassoc Wforall Wunderscore
  Wu Wlparen Wlambda Wj Wev
  IDENTIFIER Wodef Wempty_r Wempty

%%

tExprEof: a=tExpr Weof {a}
oExprEof: a=oExpr Weof {a}

command: c=command0 
  { Error.Position($startpos, $endpos), c }

command0:
| Weof
    { raise Error.Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KUlevel eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WPrint Kulevel u=uExpr Wperiod
    { Toplevel.UPrint u }
| WPrint Wtype t=tExpr Wperiod
    { Toplevel.TPrint t }
| WPrint o=oExpr Wperiod
    { Toplevel.OPrint o }
| WCheck Kulevel u=uExpr Wperiod
    { Toplevel.UCheck u }
| WCheck Wtype t=tExpr Wperiod
    { Toplevel.TCheck t }
| WCheck o=oExpr Wperiod
    { Toplevel.OCheck o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WtAlpha t1=tExpr Wequalequal t2=tExpr Wperiod
    { Toplevel.TAlpha (t1, t2) }
| WoAlpha o1=oExpr Wequalequal o2=oExpr Wperiod
    { Toplevel.OAlpha (o1, o2) }
| WuAlpha u1=uExpr Wequalequal u2=uExpr Wperiod
    { Toplevel.UAlpha (u1, u2) }
| WTau o=oExpr Wperiod
    { Toplevel.Type o }

| WDefine Wtype name=IDENTIFIER parms=parmList Wcolonequal t=tExpr Wperiod 
    { Toplevel.Definition (TDefinition (Ident name,(fixParmList parms,t))) }
| WDefine name=IDENTIFIER parms=parmList Wcolonequal o=oExpr Wcolon t=tExpr Wperiod 
    { Toplevel.Definition (ODefinition (Ident name,(fixParmList parms,o,t))) }

| WDefine Wtype Wequality name=IDENTIFIER parms=parmList Wcolonequal t1=tExpr Wequalequal t2=tExpr Wperiod 
    { Toplevel.Definition (TeqDefinition (Ident name,(fixParmList parms,t1,t2))) }
| WDefine Wequality name=IDENTIFIER parms=parmList Wcolonequal o1=oExpr Wequalequal o2=oExpr Wcolon t=tExpr Wperiod 
    { Toplevel.Definition (OeqDefinition (Ident name,(fixParmList parms,o1,o2,t))) }

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
oParm: vars=nonempty_list(IDENTIFIER) Wcolon t=tExpr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=uExpr Wequal v=uExpr 
    { (u,v) }
| v=uExpr Wgreaterequal u=uExpr 
    { nowhere (APPLY(UU UU_max, [ u; v])), v }
| u=uExpr Wlessequal v=uExpr 
    { nowhere (APPLY(UU UU_max, [ u; v])), v }
| v=uExpr Wgreater u=uExpr 
    { nowhere (APPLY(UU UU_max, [ nowhere (APPLY( UU (UU_plus 1),[u])); v])), v }
| u=uExpr Wless v=uExpr 
    { nowhere (APPLY(UU UU_max, [ nowhere (APPLY( UU (UU_plus 1),[u])); v])), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 


var: oVar0 { Error.Position($startpos, $endpos), $1 }
oVar0: IDENTIFIER { Var $1 }
tVar0: IDENTIFIER { Var $1 }
uVar0: IDENTIFIER { Var $1 }

oExpr: o=oExpr0
    { with_pos (Error.Position($startpos, $endpos)) o }
| o=parenthesized(oExpr) 
    {o}
oExpr0:
| Wunderscore
    { make_OO_emptyHole }
| x=oVar0
    { make_Variable x }
| Wu Wlparen u=euExpr Wrparen
    { make_OO_u u }
| Wj Wlparen u=euExpr Wcomma v=euExpr Wrparen
    { make_OO_j u v }
| Wev x=var Wrbracket Wlparen f=oExpr Wcomma o=oExpr Wcomma t=tExpr Wrparen
    { make_OO_ev f o (x,t) }
| Wev Wunderscore Wrbracket Wlparen f=oExpr Wcomma o=oExpr Wcomma t=tExpr Wrparen
    { make_OO_ev f o ((Error.Nowhere, VarUnused), t) }
| f=oExpr o=oExpr
    %prec Prec_application
    { make_OO_ev_hole f o }
| Wlambda x=var Wrbracket Wlparen t=tExpr Wcomma o=oExpr Wrparen
    { make_OO_lambda t (x,o) }
| Klambda x=var Wcolon t=tExpr Wcomma o=oExpr
    %prec Klambda
    { make_OO_lambda t (x,o) }
| Wforall x=var Wrbracket Wlparen u1=euExpr Wcomma u2=euExpr Wcomma o1=oExpr Wcomma o2=oExpr Wrparen
    { make_OO_forall u1 u2 o1 (x,o2) }
| Kforall x=var Wcolon Wstar o1=oExpr Wcomma o2=oExpr (* not sure about this syntax *)
    %prec Kforall
    { make_OO_forall (nowhere (make_UU UU_EmptyHole [])) (nowhere (make_UU UU_EmptyHole [])) o1 (x,o2) }
| Wempty Wlparen Wrparen
    { make_OO_empty }
| Wempty_r Wlparen t=tExpr Wcomma o=oExpr Wrparen
    { make_OO_empty_r t o }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) 
    Wrparen { make_OO_def_app name u [] [] }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) Wsemi
    t=separated_list(Wcomma,tExpr) 
    Wrparen { make_OO_def_app name u t [] }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) Wsemi
    t=separated_list(Wcomma,tExpr) Wsemi
    o=separated_list(Wcomma,oExpr) 
    Wrparen { make_OO_def_app name u t o }

tExpr: t=tExpr0 
    { with_pos (Error.Position($startpos, $endpos)) t }
| t=parenthesized(tExpr)
    { t }
tExpr0:
| Wunderscore
    { make_TT_EmptyHole }
| t=tVar0
    { make_Variable t }
| WEl Wlparen o=oExpr Wrparen
    { make_TT_El o }
| Wstar o=oExpr
    { make_TT_El o }
| WU Wlparen u=euExpr Wrparen
    { make_TT_U u }
| WPi x=var Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wrparen 
    { make_TT_Pi t1 (x,t2) }
| KPi x=var Wcolon t1=tExpr Wcomma t2=tExpr
    %prec KPi
    { make_TT_Pi t1 (x,t2) }
| t=tExpr Warrow u=tExpr
    { make_TT_Pi t ((Error.Nowhere, VarUnused),u) }
| WSigma x=var Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wrparen
    { make_TT_Sigma t1 (x,t2) }
| KSigma x=var Wcolon t1=tExpr Wcomma t2=tExpr
    %prec KSigma
    { make_TT_Sigma t1 (x,t2) }
| WCoprod Wlparen t1=tExpr Wcomma t2=tExpr Wrparen
    { make_TT_Coprod t1 t2 }
| WCoprod2 x1=var Wcomma x2=var Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wcomma s1=tExpr Wcomma s2=tExpr Wcomma o=oExpr Wrparen
    { make_TT_Coprod2 t1 t2 (x1,s1) (x2,s2) o }
| WEmpty Wlparen Wrparen 
    { make_TT_Empty }
| WIC x=var Wcomma y=var Wcomma z=var Wrbracket
    Wlparen tA=tExpr Wcomma a=oExpr Wcomma tB=tExpr Wcomma tD=tExpr Wcomma q=oExpr Wrparen 
    { make_TT_IC tA a (x,tB,(y,tD,(z,q))) }
| WId Wlparen t=tExpr Wcomma a=oExpr Wcomma b=oExpr Wrparen 
    { make_TT_Id t a b }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) 
    Wrparen { make_TT_def_app name u [] [] }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) Wsemi
    t=separated_list(Wcomma,tExpr) 
    Wrparen { make_TT_def_app name u t [] }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,euExpr) Wsemi
    t=separated_list(Wcomma,tExpr) Wsemi
    o=separated_list(Wcomma,oExpr) 
    Wrparen { make_TT_def_app name u t o }
euExpr: u=uExpr
    { u }
uExpr: u=uExpr0 
    { POS(Error.Position($startpos, $endpos), u) }
| u=parenthesized(uExpr)
    {u}
uExpr0:
| Wunderscore
    { APPLY(UU UU_EmptyHole,[]) }
| u=uVar0
    { Variable u }
| u=uExpr Wplus n=Nat
    { APPLY(UU (UU_plus n), [u]) }
| Kumax Wlparen u=uExpr Wcomma v=uExpr Wrparen
    { APPLY(UU UU_max,[u;v])  }
