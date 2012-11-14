%{
open Typesystem

type parm =
  | UParm of uContext
  | TParm of tContext
  | OParm of oContext

let fixParmList (p:parm list) : context =
  let rec fix us ts os p =
    match p with 
    | UParm u :: p -> 
	if List.length ts > 0 or List.length os > 0 then raise (GeneralError "expected ulevel variables first");
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
	| _ -> raise (Typesystem.Unimplemented "merging of ulevel variable lists")
	in Context(uc,tc,oc))
  in fix [] [] [] p

%}
%start command derivation unusedtokens
%type <Typesystem.derivation> derivation
%type <Toplevel.command> command
%type <unit> unusedtokens
%token <string> Var_token
%token <int> Nat
%token Wlparen Wrparen Wlbracket Wrbracket Wplus Wcomma Wperiod Wslash Wcolon Wstar Warrow Wequal Wturnstile Wtriangle Wcolonequal
%token Wlbrace Wrbrace
%token Wgreaterequal Wgreater Wlessequal Wless Wsemi
%token Kulevel Kumax KType KPi Klambda Kj
%token WEl WPi Wev Wu Wj WU Wlambda Wforall WSigma WCoprod WCoprod2 WEmpty Wempty WIC WId
%token WTau WPrint_t WPrint_o WPrint_u WDefine WDeclare WShow WExit
%token Wflush
%token Prec_application

/* precedences, lowest first */
%right KPi
%right Warrow
%left Prec_application
%right Klambda
%nonassoc Kj
%nonassoc Var_token Wlparen Wev Wu Wj Wlambda Wforall

%%

command:
| WPrint_t t = topTExpr Wperiod { Toplevel.Print_t t }
| WPrint_o o = topOExpr Wperiod { Toplevel.Print_o o }
| WPrint_u u = uLevel Wperiod { Toplevel.Print_u u }
| WTau topOExpr Wperiod { Toplevel.Type $2 }
| WDeclare Var_token parmList Wcolonequal topTExpr Wperiod { Toplevel.Notation (Declaration (Ident $2,fixParmList $3,$5)) }
| WDefine Var_token parmList Wcolonequal topOExpr Wperiod { Toplevel.Notation (Definition (Ident $2,fixParmList $3,$5,(Tvariable TVarDummy, Position($startpos, $endpos)))) }
| WDefine Var_token parmList Wcolonequal topOExpr Wcolon tExpr Wperiod { Toplevel.Notation (Definition (Ident $2,fixParmList $3,$5,$7)) }
| WShow Wperiod { Toplevel.Show }
| WExit Wperiod { Toplevel.Exit }

topTExpr : tExpr { Fillin.tfillin [] $1 }
topOExpr : oExpr { Fillin.ofillin [] $1 }

unusedtokens: Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile Wempty Wflush Wlbrace Wrbrace Wslash Wtriangle Wturnstile { () }

varList:
| Var_token { [$1] }
| Var_token Wcomma varList { $1 :: $3 }
uParm: varList Wcolon Kulevel uEquationList { UParm (UContext ((List.map (fun s -> UVar s) $1),$4)) }
tParm: varList Wcolon KType { TParm (List.map (fun s -> TVar s) $1) }
oParm: varList Wcolon tExpr { OParm (List.map (fun s -> (OVar s,$3)) $1) }

uEquationList: l=semi_and_uEquation* {l}
semi_and_uEquation: Wsemi; e=uEquation; {e}
uEquation:
| uLevel Wequal uLevel { ($1,$3) }
| uLevel Wgreaterequal uLevel { (Umax($1,$3),$1) }
| uLevel Wlessequal uLevel { (Umax($1,$3),$3) }
| uLevel Wgreater uLevel { (Umax($1,Uplus($3,1)),$1) }
| uLevel Wless uLevel { (Umax(Uplus($1,1),$3),$3) }

parmList:
| { [] }
| Wlparen parm Wrparen parmList { $2 :: $4 }
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

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

oExpr: mark_position(oExpr0) {$1}
oExpr0:
| Wlparen oExpr0 Wrparen { $2 }
| oVar { Ovariable $1 }
| Wu Wlparen uLevel Wrparen { O_u $3 }
| Wj Wlparen uLevel Wcomma uLevel Wrparen { O_j($3,$5) }
| Kj Wlparen uLevel Wcomma uLevel Wrparen { O_j($3,$5) }
| Wev oVar Wrbracket Wlparen oExpr Wcomma oExpr Wcomma tExpr Wrparen { O_ev($5,$7,($2,$9)) }
| oExpr oExpr %prec Prec_application { O_ev($1,$2,(OVarDummy,(Tvariable TVarDummy, Position($startpos, $endpos)))) }
| Wlambda oVar Wrbracket Wlparen tExpr Wcomma oExpr Wrparen { O_lambda($5,($2,$7)) }
| Klambda oVar Wcolon tExpr Wcomma oExpr %prec Klambda { O_lambda($4,($2,$6)) }
| Wforall oVar Wrbracket Wlparen uLevel Wcomma uLevel Wcomma oExpr Wcomma oExpr Wrparen { O_forall($5,$7,$9,($2,$11)) }
tExpr: mark_position(tExpr0) {$1}
tExpr0:
| Wlparen tExpr0 Wrparen { $2 }
| tVar { Tvariable $1 }
| WEl Wlparen oExpr Wrparen { El $3 }
| Wstar oExpr { El $2 }
| WU Wlparen uLevel Wrparen { T_U $3 }
| WPi oVar Wrbracket Wlparen tExpr Wcomma tExpr Wrparen { Pi($5,($2,$7)) }
| KPi oVar Wcolon tExpr Wcomma tExpr %prec KPi { Pi($4,($2,$6)) }
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
mark_position(a): x=a { x, Position($startpos, $endpos) }
