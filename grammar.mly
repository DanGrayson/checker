%{
open Typesystem

type parm =
  | UParm of uContext
  | TParm of tContext
  | OParm of oContext

let fixParmList (p:parm list) : uContext * tContext * oContext =
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
%start command derivation unusedtokens
%type <Typesystem.derivation> derivation
%type <Toplevel.command> command
%type <unit> unusedtokens
%token <string> Var_token 
%token <Typesystem.tVar> TVar_token
%token <Typesystem.uVar> UVar_token 
%token <int> Nat
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequal Wturnstile Wtriangle Wcolonequal
%token Wlbrace Wrbrace Wbar Wunderscore
%token Wgreaterequal Wgreater Wlessequal Wless Wsemi
%token Kulevel KType KPi Klambda Kj KSigma
%token WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2 WEmpty Wempty WIC WId
%token WTau WPrint_t WPrint_o WPrint_u WDefine WDeclare WShow WExit WtVariable WuVariable
%token Wflush
%token Prec_application

/* precedences, lowest first */
%right KPi KSigma
%right Warrow
%left Wbar
%left Wplus
%left Prec_application
%right Klambda
%nonassoc Kj
%nonassoc Var_token Wlparen Wev Wu Wj Wlambda Wforall

%%

command:
| WtVariable vars=nonempty_list(Var_token) Wperiod
    { Toplevel.TVariable vars }
| WuVariable vars=nonempty_list(Var_token) eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }
| WPrint_t t = topTExpr Wperiod
    { Toplevel.Print_t t }
| WPrint_o o = topOExpr Wperiod
    { Toplevel.Print_o o }
| WPrint_u u = uLevel Wperiod
    { Toplevel.Print_u u }
| WTau o=topOExpr Wperiod
    { Toplevel.Type o }
| WDeclare name=Var_token parms=parmList Wcolonequal t=topTExpr Wperiod 
    { Toplevel.Notation (TDefinition (Ident name,(fixParmList parms,t))) }
| WDefine v=Var_token p=parmList Wcolonequal o=oExpr Wperiod 
    {
     let (uc,tc,oc) = fixParmList p in
     let o = List.fold_right (fun (x,t) o -> nowhere( O_lambda (t, (x,o)))) oc o in
     let o = Fillin.ofillin [] o in
     let t = Tau.tau [] o in
     Toplevel.Notation (
     ODefinition (Ident v,((uc,tc,emptyOContext),o,t))
    ) 
   }
| WDefine name=Var_token parms=parmList Wcolonequal o=topOExpr Wcolon t=tExpr Wperiod 
    { Toplevel.Notation (ODefinition (Ident name,(fixParmList parms,o,t))) }
| WShow Wperiod 
    { Toplevel.Show }
| WExit Wperiod
    { Toplevel.Exit }

topTExpr : tExpr
    { Fillin.tfillin [] $1 }
topOExpr : oExpr
    { Fillin.ofillin [] $1 }

unusedtokens: Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile Wempty Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile TVar_token UVar_token { () }

uParm: vars=nonempty_list(Var_token) Wcolon Kulevel eqns=preceded(Wsemi,uEquation)*
    { UParm (UContext ((List.map make_uVar vars),eqns)) }
tParm: vars=nonempty_list(Var_token) Wcolon KType 
    { TParm (List.map make_tVar vars) }
oParm: vars=nonempty_list(Var_token) Wcolon t=tExpr 
    { OParm (List.map (fun s -> (OVar s,t)) vars) }

uEquation:
| u=uLevel Wequal v=uLevel 
    { (u,v) }
| u=uLevel Wgreaterequal v=uLevel 
    { (Umax(u,v),u) }
| u=uLevel Wlessequal v=uLevel 
    { (Umax(u,v),v) }
| u=uLevel Wgreater v=uLevel 
    { (Umax(u,Uplus(v,1)),u) }
| u=uLevel Wless v=uLevel 
    { (Umax(Uplus(u,1),v),v) }

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

oVar: Var_token { OVar $1 }

tVar: 					(* we have to choose one approach or the other: *)
| Var_token { TVar $1 }
| TVar_token { $1 }

uVar: Var_token { UVar $1 }

oExpr: o=oExpr0
    {o, Position($startpos, $endpos)}
| o=parenthesized(oExpr) 
    {o}
oExpr0:
| x=oVar
    { Ovariable x }
| Wu Wlparen u=uLevel Wrparen
    { O_u u }
| Wj Wlparen u=uLevel Wcomma v=uLevel Wrparen
    { O_j(u,v) }
| Kj Wunderscore Wlparen u=uLevel Wcomma v=uLevel Wrparen
    { O_j(u,v) }
| Wev x=oVar Wrbracket Wlparen f=oExpr Wcomma o=oExpr Wcomma t=tExpr Wrparen
    { O_ev(f,o,(x,t)) }
| f=oExpr o=oExpr
    %prec Prec_application
    { O_ev(f,o,(OVarDummy,(Tvariable TVarDummy, Nowhere))) }
| Wlambda x=oVar Wrbracket Wlparen t=tExpr Wcomma o=oExpr Wrparen
    { O_lambda(t,(x,o)) }
| Klambda x=oVar Wcolon t=tExpr Wcomma o=oExpr
    %prec Klambda
    { O_lambda(t,(x,o)) }
| Wforall x=oVar Wrbracket Wlparen u1=uLevel Wcomma u2=uLevel Wcomma o1=oExpr Wcomma o2=oExpr Wrparen
    { O_forall(u1,u2,o1,(x,o2)) }

tExpr: t=tExpr0 
    {t, Position($startpos, $endpos)}
| t=parenthesized(tExpr)
    {t}
tExpr0:
| t=tVar
    { Tvariable t }
| WEl Wlparen o=oExpr Wrparen
    { El o }
| Wstar o=oExpr
    { El o }
| WU Wlparen u=uLevel Wrparen
    { T_U u }
| WPi x=oVar Wrbracket Wlparen t1=tExpr Wcomma t2=tExpr Wrparen 
    { Pi(t1,(x,t2)) }
| KPi x=oVar Wcolon t1=tExpr Wcomma t2=tExpr
    %prec KPi
    { Pi(t1,(x,t2)) }
| t=tExpr Warrow u=tExpr
    { Pi(t,(OVarDummy,u)) }
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
uLevel:
| Wlparen u=uLevel Wrparen 
    { u }
| n=Nat
    { Unumeral n }
| u=uVar
    { Uvariable u }
| u=uLevel Wplus n=Nat
    { Uplus (u,n) }
| u=uLevel Wbar v=uLevel
    { Umax (u,v)  }
