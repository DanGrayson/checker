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
	if List.length ts > 0 or List.length os > 0 then raise (GeneralError "expected universe-level variables first");
	fix (u::us) ts os p
    | TParm t :: p -> 
	if List.length os > 0 then raise (Typesystem.Unimplemented "a type parameter after an object parameter");
	fix us (t::ts) os p
    | OParm o :: p -> fix us ts (o::os) p
    | [] -> ( 
	let tc = List.flatten (List.rev_append ts [])
	and oc = List.flatten (List.rev_append os [])
	and uc = match (List.rev_append us []) with
	| [] -> emptyUContext
	| (uc :: []) -> uc
	| _ -> raise (Typesystem.Unimplemented "merging of universe level variable lists")
	in (uc,tc,oc))
  in fix [] [] [] p

%}
%start command derivation unusedtokens uExprEof tExprEof oExprEof
%type <Typesystem.derivation> derivation
%type <Toplevel.command> command
%type <Typesystem.uExpr> uExprEof
%type <Typesystem.tExpr> tExprEof
%type <Typesystem.oExpr> oExprEof
%token <int> Nat Wunderscore_numeral
%type <unit> unusedtokens
%token <string> IDENTIFIER
%token <Typesystem.uVar> UVar_token 
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequalequal Wequal Wturnstile Wtriangle Wcolonequal
%token Wlbrace Wrbrace Wbar Wunderscore
%token Wgreaterequal Wgreater Wlessequal Wless Wsemi
%token KUniv Kumax KType KPi Klambda KSigma
%token WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2 WEmpty Wempty Wempty_r WIC WId
%token WTau WtPrint WoPrint WuPrint WoDefinition WtDefinition WShow WExit WVariable WoAlpha WtAlpha WuAlpha Weof
%token WuCheck WtCheck WoCheck
%token Wflush
%token Prec_application
%token Wudef Wtdef Wodef

/* precedences, lowest first */
%right KPi KSigma
%right Warrow
%left Prec_application
%right Klambda
%nonassoc Wforall Wunderscore Wunderscore_numeral Nat Wu Wlparen Wlambda Wj Wev IDENTIFIER Wodef Wempty_r Wempty

%%

uExprEof: a=uExpr Weof {a}
tExprEof: a=tExpr Weof {a}
oExprEof: a=oExpr Weof {a}

command:
| Weof
    { raise Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KType Wperiod
    { Toplevel.TVariable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Wcolon KUniv eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WuPrint u=uExpr Wperiod
    { Toplevel.UPrint u }
| WtPrint t=tExpr Wperiod
    { Toplevel.TPrint t }
| WoPrint o=oExpr Wperiod
    { Toplevel.OPrint o }
| WuCheck u=uExpr Wperiod
    { Toplevel.UCheck u }
| WtCheck t=tExpr Wperiod
    { Toplevel.TCheck t }
| WoCheck o=oExpr Wperiod
    { Toplevel.OCheck o }
| WtAlpha t1=tExpr Wequalequal t2=tExpr Wperiod
    { Toplevel.TAlpha (t1, t2) }
| WoAlpha o1=oExpr Wequalequal o2=oExpr Wperiod
    { Toplevel.OAlpha (o1, o2) }
| WuAlpha u1=uExpr Wequalequal u2=uExpr Wperiod
    { Toplevel.UAlpha (u1, u2) }
| WTau o=oExpr Wperiod
    { Toplevel.Type o }
| WtDefinition name=IDENTIFIER parms=parmList Wcolonequal t=tExpr Wperiod 
    { Toplevel.Definition (TDefinition (Ident name,(fixParmList parms,t))) }
| WoDefinition v=IDENTIFIER p=parmList Wcolonequal o=oExpr Wperiod 
    {
     let (uc,tc,oc) = fixParmList p in
     let o = List.fold_right (fun (x,t) o -> nowhere( O_lambda (t, (nowhere x,o)))) oc o in
     Toplevel.Definition ( ODefinition (Ident v,((uc,tc,emptyOContext),o,nowhere TEmptyHole)) ) 
   }
| WoDefinition name=IDENTIFIER parms=parmList Wcolonequal o=oExpr Wcolon t=tExpr Wperiod 
    { Toplevel.Definition (ODefinition (Ident name,(fixParmList parms,o,t))) }
| WShow Wperiod 
    { Toplevel.Show }
| WExit Wperiod
    { Toplevel.Exit }

unusedtokens: Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile Wempty Wempty_r Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile Wbar UVar_token { () }

uParm: vars=nonempty_list(IDENTIFIER) Wcolon KUniv eqns=preceded(Wsemi,uEquation)*
    { UParm (UContext ((List.map make_uVar vars),eqns)) }
tParm: vars=nonempty_list(IDENTIFIER) Wcolon KType 
    { TParm (List.map make_tVar vars) }
oParm: vars=nonempty_list(IDENTIFIER) Wcolon t=tExpr 
    { OParm (List.map (fun s -> (OVar s,t)) vars) }

uEquation:
| u=uExpr Wequal v=uExpr 
    { (u,v) }
| u=uExpr Wgreaterequal v=uExpr 
    { nowhere(Umax(u,v)), u }
| u=uExpr Wlessequal v=uExpr 
    { nowhere(Umax(u,v)), v }
| u=uExpr Wgreater v=uExpr 
    { nowhere(Umax(u,nowhere(Uplus(v,1)))), u }
| u=uExpr Wless v=uExpr 
    { nowhere(Umax(nowhere(Uplus(u,1)),v)), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

derivation_list:
| Wlbracket e=derivation_list_entries Wrbracket { e }
| Wlbracket Wrbracket { [] }
derivation_list_entries:
| derivation 
    { [$1] }
| derivation Wcomma derivation_list
    { $1 :: $3 }
derivation:
| Wlparen n=Nat Wcomma Wcomma derivs=derivation_list Wrparen 
    { inferenceRule(n,RPNone,derivs) }

oVar: oVar0 { Position($startpos, $endpos), $1 }
oVar0: IDENTIFIER { OVar $1 }
tVar0: IDENTIFIER { TVar $1 }
uVar0: IDENTIFIER { UVar $1 }

oExpr: o=oExpr0
    {Position($startpos, $endpos), o}
| o=parenthesized(oExpr) 
    {o}
oExpr0:
| Wunderscore
    { OEmptyHole }
| Wunderscore_numeral 
    { ONumberedEmptyHole $1 }
| x=oVar0
    { Ovariable x }
| Wu Wlparen u=uExpr Wrparen
    { O_u u }
| Wj Wlparen u=uExpr Wcomma v=uExpr Wrparen
    { O_j(u,v) }
| Wev x=oVar Wrbracket Wlparen f=oExpr Wcomma o=oExpr Wcomma t=tExpr Wrparen
    { O_ev(f,o,(x,t)) }
| Wev Wunderscore Wrbracket Wlparen f=oExpr Wcomma o=oExpr Wcomma t=tExpr Wrparen
    { O_ev(f,o,(nowhere OVarUnused,t)) }
| f=oExpr o=oExpr
    %prec Prec_application
    { O_ev(f,o,(nowhere OVarEmptyHole,nowhere TEmptyHole)) }
| Wlambda x=oVar Wrbracket Wlparen t=tExpr Wcomma o=oExpr Wrparen
    { O_lambda(t,(x,o)) }
| Klambda x=oVar Wcolon t=tExpr Wcomma o=oExpr
    %prec Klambda
    { O_lambda(t,(x,o)) }
| Wforall x=oVar Wrbracket Wlparen u1=uExpr Wcomma u2=uExpr Wcomma o1=oExpr Wcomma o2=oExpr Wrparen
    { O_forall(u1,u2,o1,(x,o2)) }
| Wempty Wlparen Wrparen
    { O_empty }
| Wempty_r Wlparen t=tExpr Wcomma o=oExpr Wrparen
    { O_empty_r(t,o) }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) 
    Wrparen { O_def(name,u,[],[]) }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) Wsemi
    t=separated_list(Wcomma,tExpr) 
    Wrparen { O_def(name,u,t,[]) }
| Wodef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) Wsemi
    t=separated_list(Wcomma,tExpr) Wsemi
    o=separated_list(Wcomma,oExpr) 
    Wrparen { O_def(name,u,t,o) }
| n=Nat
    { Onumeral n }			(* experimental *)

tExpr: t=tExpr0 
    {Position($startpos, $endpos), t}
| t=parenthesized(tExpr)
    {t}
tExpr0:
| Wunderscore
    { TEmptyHole }
| Wunderscore_numeral 
    { TNumberedEmptyHole $1 }
| t=tVar0
    { Tvariable t }
| WEl Wlparen o=oExpr Wrparen
    { El o }
| Wstar o=oExpr
    { El o }
| WU Wlparen u=uExpr Wrparen
    { T_U u }
| WPi x=oVar Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wrparen 
    { Pi(t1,(x,t2)) }
| KPi x=oVar Wcolon t1=tExpr Wcomma t2=tExpr
    %prec KPi
    { Pi(t1,(x,t2)) }
| t=tExpr Warrow u=tExpr
    { Pi(t,(nowhere OVarUnused,u)) }
| WSigma x=oVar Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wrparen
    { Sigma(t1,(x,t2)) }
| KSigma x=oVar Wcolon t1=tExpr Wcomma t2=tExpr
    %prec KSigma
    { Sigma(t1,(x,t2)) }
| WCoprod Wlparen t1=tExpr Wcomma t2=tExpr Wrparen
    { T_Coprod(t1,t2) }
| WCoprod2 x1=oVar Wcomma x2=oVar Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wcomma s1=tExpr Wcomma s2=tExpr Wcomma o=oExpr Wrparen
    { T_Coprod2(t1,t2,(x1,s1),(x2,s2),o) }
| WEmpty Wlparen Wrparen 
    { T_Empty }
| WIC x=oVar Wcomma y=oVar Wcomma z=oVar Wrbracket
    Wlparen tA=tExpr Wcomma a=oExpr Wcomma tB=tExpr Wcomma tD=tExpr Wcomma q=oExpr Wrparen 
    { T_IC(tA,a,(x,tB,(y,tD,(z,q)))) }
| WId Wlparen t=tExpr Wcomma a=oExpr Wcomma b=oExpr Wrparen 
    { Id(t,a,b) }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) 
    Wrparen { T_def(name,u,[],[]) }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) Wsemi
    t=separated_list(Wcomma,tExpr) 
    Wrparen { T_def(name,u,t,[]) }
| Wtdef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) Wsemi
    t=separated_list(Wcomma,tExpr) Wsemi
    o=separated_list(Wcomma,oExpr) 
    Wrparen { T_def(name,u,t,o) }
uExpr: u=uExpr0 
    {Position($startpos, $endpos), u}
| u=parenthesized(uExpr)
    {u}
uExpr0:
| Wunderscore
    { UEmptyHole }
| Wunderscore_numeral
    { UNumberedEmptyHole $1 }
| u=uVar0
    { Uvariable u }
| u=uExpr Wplus n=Nat
    { Uplus (u,n) }
| Kumax Wlparen u=uExpr Wcomma v=uExpr Wrparen
    { Umax (u,v)  }
| Wudef name=IDENTIFIER Wrbracket Wlparen 
    u=separated_list(Wcomma,uExpr) 
    Wrparen { U_def(name,u) }
