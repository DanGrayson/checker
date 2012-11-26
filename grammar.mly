%{ 

open Typesystem
open Helpers
open Grammar0

%}
%start command ts_exprEof lf_exprEof
%type <Toplevel.command> command
%type <Typesystem.expr> ts_exprEof lf_exprEof
%type <Typesystem.expr list> arglist
%type <Typesystem.canonical_type_family> canonical_type_family
%token <int> Nat
%token <string> IDENTIFIER LABEL LABEL_SEMI
%token <string * int> DEF_APP
%token

  Wlparen Wrparen Wrbracket Wplus Wcomma Wperiod  Wcolon Wstar
  Warrow Wequalequal Wequal   Wcolonequal 
   Wunderscore WF_Print WRule Wgreaterequal Wgreater Wlessequal Wless Wsemi
  KUlevel Kumax KType KPi Klambda KSigma WTau WPrint WDefine WShow WEnd
  WVariable WAlpha Weof Watat WCheck WCheckUniverses  Prec_application

/* precedences, lowest first */
%right
  KPi KSigma
%right
  Warrow
%nonassoc
  Wstar				/* we want  [*f x] to be [*(f x)]  and  [*x->y] to be [( *x )->y]  */
%left
  Prec_application
%right
  Klambda
%nonassoc
  Wunderscore Wplus Wlparen IDENTIFIER Kumax Watat LABEL_SEMI LABEL DEF_APP

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
| Wlparen Klambda v=variable Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }
| Wlparen Klambda v=variable_unused Wcomma body=lf_expr Wrparen
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
| l=LABEL
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

| WRule num=Nat name=IDENTIFIER Wcolon t=canonical_type_family Wperiod
    { Toplevel.Rule (num,name,t) }

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
variable_or_unused:
| bare_variable_or_unused
    { Error.Position($startpos, $endpos), $1 }
ts_expr:
| bare_ts_expr
    { with_pos (Error.Position($startpos, $endpos)) $1 }
| parenthesized(ts_expr) 
    {$1}
| Watat e=lf_expr
    {e}
arglist:
| Wlparen a=separated_list(Wcomma,ts_expr) Wrparen
    {a}
bare_variable:
| IDENTIFIER
    { Var $1 }
bare_variable_or_unused:
| v=bare_variable
    {v}
| Wunderscore
    { VarUnused }
bare_ts_expr:
| bare_variable
    { Variable $1 }
| Wunderscore
    { new_hole' () }
| f=ts_expr o=ts_expr
    %prec Prec_application
    { make_OO_ev f o ((Error.Nowhere, VarUnused), with_pos (Error.Position($startpos, $endpos)) (new_hole'())) }
| Klambda x=variable Wcolon t=ts_expr Wcomma o=ts_expr
    %prec Klambda
    { make_OO_lambda t (x,o) }
| Wstar o=ts_expr
    { make_TT_El o }
| KPi x=variable Wcolon t1=ts_expr Wcomma t2=ts_expr
    %prec KPi
    { make_TT_Pi t1 (x,t2) }
| t=ts_expr Warrow u=ts_expr
    { make_TT_Pi t ((Error.Nowhere, VarUnused),u) }
| KSigma x=variable Wcolon t1=ts_expr Wcomma t2=ts_expr
    %prec KSigma
    { make_TT_Sigma t1 (x,t2) }
| u=ts_expr Wplus n=Nat
    { APPLY(U (U_plus n), [u]) }
| Kumax Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { APPLY(U U_max,[u;v])  }
| def=DEF_APP a=arglist
    { let (name,aspect) = def in APPLY(Defapp(name,aspect),a) }
| name=LABEL a=arglist
    {
     let label = 
       try List.assoc ("[" ^ name ^ "]") label_strings with Not_found -> $syntaxerror
     in
     match head_to_vardist label with
     | None -> APPLY(label,a)
     | Some (n,_) ->
	 if n = 0 then APPLY(label,a)
	 else
	   raise (Error.TypingError
		    ( Error.Position($startpos, $endpos),
		      "expected " ^ (string_of_int n) ^ " variable" ^ (if n != 1 then "s" else "")));
	 
   }
| name=LABEL_SEMI vars=separated_list(Wcomma,variable_or_unused) Wrbracket args=arglist
    {
     let label = 
       try List.assoc ("[" ^ name ^ "]") label_strings with Not_found -> $syntaxerror
     in
     match head_to_vardist label with
     | None -> raise (Error.TypingError (Error.Position($startpos, $endpos), "expected no variables"))
     | Some (nvars,varindices) ->
	 if nvars != List.length vars then
	   raise (Error.TypingError
		    ( Error.Position($startpos, $endpos),
		      "expected " ^ (string_of_int nvars) ^ " variable" ^ (if nvars != 1 then "s" else "")));
	 let nargs = List.length varindices
	 in
	 if List.length args != nargs then
	   raise (Error.TypingError
		    ( Error.Position($startpos, $endpos),
		      "expected " ^ (string_of_int nargs) ^ " argument" ^ (if nargs != 1 then "s" else "")));
	 let args = List.map2 (
	   fun indices arg ->
	     (* example: indices = [0;1], change arg to (LAMBDA v_0, (LAMBDA v_1, arg)) *)
	     List.fold_right (
	     fun index arg -> LAMBDA( List.nth vars index, arg)
		 ) indices arg
	  ) varindices args
	 in
	 APPLY(label,args)
   }
