%{ 
open Error
open Typesystem
open Names
open Helpers
open Definitions
%}
%start command ts_exprEof
%type <Toplevel.command> command
%type <Typesystem.ts_expr> ts_exprEof ts_expr
%type <Typesystem.bare_ts_expr> bare_ts_expr
%type <Typesystem.ts_expr list> arglist
%type <Typesystem.lf_type> lf_type
%type <Typesystem.lf_expr> lf_expr
%token <int> NUMBER
%token <string> IDENTIFIER CONSTANT CONSTANT_SEMI
%token <Typesystem.var> VARIABLE
%token

  Wlparen Wrparen Wrbracket Wlbracket Wcomma Wperiod COLON Wstar Warrow Wmapsto
  Wequal COLONequal Wunderscore WRule Wgreaterequal Wgreater Wlessequal Wless
  Wsemi KUlevel Kumax KType Ktype KPi Klambda KSigma WCheck WDefine WShow WEnd
  WVariable WAlpha Weof WCheckUniverses Wtilde KSingleton Axiom Wdollar W_LF W_TS

/* precedences, lowest first */
%right

  Reduce_binder

%right

  Warrow

%nonassoc

  /* we want  [*f x] to be [*(f x)]  and  [*x->y] to be [( *x )->y]  */
  Reduce_star

%nonassoc

  /* We want [f x IDENTIFIER] to reduce to [(f x) IDENTIFIER], so
     the precedence of IDENTIFIER is lower than Reduce_application. */

  IDENTIFIER

  /* These are the other tokens that can begin a TS-expression : ditto. */

  Wunderscore Wlparen Kumax CONSTANT_SEMI CONSTANT Wstar
  Klambda KSigma KPi VARIABLE

%left

  Reduce_application

%%

lf_type:
| t=bare_lf_type
    { Position($startpos, $endpos), t}
| Wlparen t=lf_type Wrparen 
    { t }

bare_lf_type:
| f=lf_type_constant args=list(lf_expr)
    { F_APPLY(f,args) }
| KPi v=bare_variable COLON a=lf_type Wcomma b=lf_type
    %prec Reduce_binder
    { F_Pi(v,a,b) }
| a=lf_type Warrow b=lf_type
   { F_Pi(VarUnused,a,b) }
| KSingleton Wlparen x=lf_expr COLON t=lf_type Wrparen
    { F_Singleton(x,t) }
| Wlbracket a=lf_expr Ktype Wrbracket
    { F_APPLY(F_istype, [a]) }
| Wlbracket a=lf_expr COLON b=lf_expr Wrbracket
    { F_APPLY(F_hastype, [a;b]) }
| Wlbracket a=lf_expr Wequal b=lf_expr COLON c=lf_expr Wrbracket
    { F_APPLY(F_object_equality, [a;b;c]) }
| Wlbracket a=lf_expr Wequal b=lf_expr Wrbracket
    { F_APPLY(F_type_equality, [a;b]) }

| Wlbracket a=lf_expr Wtilde b=lf_expr COLON KType Wrbracket
    { F_APPLY(F_type_uequality, [a;b]) }
| Wlbracket a=lf_expr Wtilde b=lf_expr Wrbracket
    { F_APPLY(F_object_uequality, [a;b]) }

lf_type_constant:
| l=IDENTIFIER 
    { 
      try List.assoc l Names.tfhead_strings 
      with 
	Not_found ->
	  Printf.fprintf stderr "%s: unknown type constant %s\n" 
	    (errfmt (Position($startpos, $endpos)))
	    l;
	  flush stderr;
	  $syntaxerror
    }

lf_expr:
| e=atomic_term
    { Phi(Position($startpos, $endpos), e)  }
| e=lf_lambda_expression
    { e }

lf_lambda_expression:
| Wlparen Klambda v=variable Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }
| Wlparen v=variable Wmapsto body=lf_lambda_expression_body Wrparen
    { LAMBDA(v,body) }
| Wlparen Klambda v=variable_unused Wcomma body=lf_expr Wrparen
    { LAMBDA(v,body) }
| Wlparen v=variable_unused Wmapsto body=lf_lambda_expression_body Wrparen
    { LAMBDA(v,body) }

lf_lambda_expression_body:
| e=lf_expr
    { e }
| v=variable Wmapsto body=lf_lambda_expression_body
    { LAMBDA(v,body) }
| v=variable_unused Wmapsto body=lf_lambda_expression_body
    { LAMBDA(v,body) }

variable_unused:
| Wunderscore
    { VarUnused }

tactic_expr:
| c=IDENTIFIER
  { c }

atomic_term:
| Wdollar name=tactic_expr
    { TacticHole (Q_name name) }
| Wdollar index=NUMBER
    { TacticHole (Q_index index) }
| bare_variable
    { APPLY(V $1,[]) }
| Wunderscore
    { new_hole () }
| Wlparen f=lf_expr_head args=list(lf_expr) Wrparen
    { APPLY(f,args) }

lf_expr_head:
| tsterm_head
    { $1 }
| bare_variable
    { V $1 }

command: c=command0 
  { Position($startpos, $endpos), c }

command0:
| Weof
    { raise Eof }
| WVariable vars=nonempty_list(IDENTIFIER) COLON KType Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) COLON KUlevel eqns=preceded(Wsemi,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }

| Axiom W_TS v=IDENTIFIER COLON t=ts_expr Wperiod
    { Toplevel.AxiomTS(v,t) }
| Axiom W_LF v=IDENTIFIER COLON t=lf_type Wperiod
    { Toplevel.AxiomLF(v,t) }
| WRule num=NUMBER name=IDENTIFIER COLON t=lf_type Wperiod
    { Toplevel.Rule (num,name,t) }

| WCheck W_LF e=lf_expr Wperiod
    { Toplevel.CheckLF e }
| WCheck W_LF Ktype e=lf_type Wperiod
    { Toplevel.CheckLFtype e }
| WCheck W_TS o=ts_expr Wperiod
    { Toplevel.Check o }
| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }
| WAlpha e1=ts_expr Wequal e2=ts_expr Wperiod
    { Toplevel.Alpha (e1, e2) }

| WDefine name=IDENTIFIER parms=parmList COLONequal t=ts_expr d1=option(preceded(Wsemi,lf_expr)) Wperiod 
    { Toplevel.TDefinition (name, parms, t, d1) }
| WDefine name=IDENTIFIER parms=parmList COLONequal o=ts_expr COLON t=ts_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t) }
| WDefine name=IDENTIFIER parms=parmList COLONequal t1=ts_expr Wequal t2=ts_expr Wperiod 
    { Toplevel.TeqDefinition (name, parms, t1, t2) }
| WDefine name=IDENTIFIER parms=parmList COLONequal o1=ts_expr Wequal o2=ts_expr COLON t=ts_expr Wperiod 
    { Toplevel.OeqDefinition (name, parms, o1, o2, t) }

| WShow Wperiod 
    { Toplevel.Show None }
| WShow n=NUMBER Wperiod 
    { Toplevel.Show (Some n) }
| WEnd Wperiod
    { Toplevel.End }

uParm: vars=nonempty_list(IDENTIFIER) COLON KUlevel eqns=preceded(Wsemi,uEquation)*
    { UParm (UContext ((List.map make_Var vars),eqns)) }
tParm: vars=nonempty_list(IDENTIFIER) COLON KType 
    { TParm (List.map make_Var vars) }
oParm: vars=nonempty_list(IDENTIFIER) COLON t=ts_expr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=ts_expr Wequal v=ts_expr 
    { (u,v) }
| v=ts_expr Wgreaterequal u=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ Phi u; Phi v])), v }
| u=ts_expr Wlessequal v=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ Phi u; Phi v])), v }
| v=ts_expr Wgreater u=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ Phi (Position($startpos, $endpos), APPLY( U U_next,[Phi u])); Phi v])), v }
| u=ts_expr Wless v=ts_expr 
    { (Position($startpos, $endpos), APPLY(U U_max, [ Phi (Position($startpos, $endpos), APPLY( U U_next,[Phi u])); Phi v])), v }

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
    { $1 }

variable_or_unused:
| bare_variable_or_unused
    { $1 }

ts_expr:
| bare_ts_expr
    { (Position($startpos, $endpos), $1) }
| parenthesized(ts_expr) 
    {$1}

tsterm_head:
| l=CONSTANT
    {
     try List.assoc ("[" ^ l ^ "]") Names.string_to_label 
     with Not_found -> 
       Printf.fprintf stderr "%s: unknown term constant [%s]\n" 
	 (errfmt (Position($startpos, $endpos)))
	 l;
       flush stderr;
       $syntaxerror 
   }

arglist:
| Wlparen a=separated_list(Wcomma,ts_expr) Wrparen
    {a}

bare_variable:
| IDENTIFIER
    { Var $1 }
| v=VARIABLE
    { v }

bare_variable_or_unused:
| v=bare_variable
    {v}
| Wunderscore
    { VarUnused }

bare_ts_expr:
| bare_variable
    { APPLY(V $1,[]) }
| Wunderscore
    { new_hole () }
| f=ts_expr o=ts_expr
    %prec Reduce_application
    { make_OO_ev f o (VarUnused, (Position($startpos, $endpos), new_hole())) }
| Klambda x=variable COLON t=ts_expr Wcomma o=ts_expr
    %prec Reduce_binder
    { make_OO_lambda t (x,o) }
| Wstar o=ts_expr
    %prec Reduce_star
    { make_TT_El o }
| KPi x=variable COLON t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_TT_Pi t1 (x,t2) }
| t=ts_expr Warrow u=ts_expr
    { make_TT_Pi t (VarUnused,u) }
| KSigma x=variable COLON t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_TT_Sigma t1 (x,t2) }
| Kumax Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { APPLY(U U_max,[Phi u;Phi v])  }
| label=tsterm_head args=arglist
    {
     match label with
     | V _ -> APPLY(label,to_atomic args)
     | _ -> (
	 match head_to_vardist label with
	 | None -> APPLY(label,to_atomic args)
	 | Some (n,_) ->
	     if n = 0 then APPLY(label,to_atomic args)
	     else
	       raise (MarkedError
			( Position($startpos, $endpos),
			  "expected " ^ (string_of_int n) ^ " variable" ^ (if n != 1 then "s" else ""))))
   }
| name=CONSTANT_SEMI vars=separated_list(Wcomma,variable_or_unused) Wrbracket args=arglist
    {
     let label = 
       try List.assoc ("[" ^ name ^ "]") Names.string_to_label 
       with Not_found -> 
	 Printf.fprintf stderr "%s: unknown term constant [%s]\n" 
	   (errfmt (Position($startpos, $endpos)))
	   name;
	 flush stderr;
	 $syntaxerror
     in
     match head_to_vardist label with
     | None -> raise (MarkedError (Position($startpos, $endpos), "expected no variables"))
     | Some (nvars,varindices) ->
	 if nvars != List.length vars then
	   raise (MarkedError
		    ( Position($startpos, $endpos),
		      "expected " ^ (string_of_int nvars) ^ " variable" ^ (if nvars != 1 then "s" else "")));
	 let nargs = List.length varindices
	 in
	 if List.length args != nargs then
	   raise (MarkedError
		    ( Position($startpos, $endpos),
		      "expected " ^ (string_of_int nargs) ^ " argument" ^ (if nargs != 1 then "s" else "")));
	 let args = List.map2 (
	   fun indices arg ->
	     (* example: indices = [0;1], change arg to (LAMBDA v_0, (LAMBDA v_1, Phi arg)) *)
	     List.fold_right (
	     fun index arg -> LAMBDA( List.nth vars index, arg)
		 ) indices (Phi arg)
	  ) varindices args
	 in
	 APPLY(label,args)
   }
 
