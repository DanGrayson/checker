%{ 
open Error
open Variables
open Typesystem
open Names
open Helpers
open Definitions

let add_sigma pos v t t' u =
  let v' = newfresh v in
  if disable_sigma then 
    F_Pi(v, t, (pos, F_Pi(v', new_pos pos (t' (var_to_lf v)), u)))
  else
    F_Pi(v, (pos, F_Sigma(v', t, t' (var_to_lf v'))), u)

%}
%start command ts_exprEof
%type <Toplevel.command> command
%type <Typesystem.lf_type> lf_type lf_type_from_ts_syntax
%type <Typesystem.lf_expr> lf_expr lf_expr_from_ts_syntax

(* for parsing a single expression *)
%type <Typesystem.lf_expr> ts_exprEof ts_expr

%token <int> NUMBER
%token <string> IDENTIFIER CONSTANT CONSTANT_SEMI
%token <Variables.var> VARIABLE
%token

  (* tokens *)

  Wlparen Wrparen Wrbracket Wlbracket Wcomma Wperiod Colon Wstar Arrow
  ArrowFromBar Wequal Colonequal Wunderscore WRule Wgreaterequal Wgreater
  Wlessequal Wless Semicolon KUlevel Kumax Type KPi Klambda KSigma WCheck
  WDefine WShow WEnd WVariable WAlpha Weof WCheckUniverses Wtilde Singleton
  Axiom Wdollar LF LFtype LFtypeTS TS Kpair Kpi1 Kpi12 Kpi122 Kpi1222 Kpi2
  Kpi22 Kpi222 Kpi2222 Wtimes DoubleBackslash Turnstile DoubleArrow DoubleColon
  Backslash DoubleArrowFromBar DoubleSemicolon

(* precedences, lowest first *)

%right

  (* we want [lambda x, lambda y, b] to be [lambda x, (lambda y, b)] *)
  (* we want [lambda x, f b] to be [lambda x, (f b)] *)
  Reduce_binder

%nonassoc

  (* we want  [*f x] to be [*(f x)]  and  [*x->y] to be [( *x )->y]  *)
  Reduce_star

%right

  (* function type *)
  (* we want [a -> b -> c] to be [a -> (b -> c)] *)

  DoubleArrowFromBar
  DoubleArrow
  Arrow

%right

  (* product type *)
  (* we want [a * b * c] to be [a * (b * c)], by analogy with [a -> b] *)
  (* we want [a * b -> c] to be [(a * b) -> c] *)

  Wtimes
  Wstar

%right

  (* substitution *)
  (* we want [x\\y\\f] to be [x\\(y\\f)] *)
  (* we want [x\y\f] to be [x\(y\f)] *)

  DoubleBackslash
  Backslash

%nonassoc

  (* These are the tokens that can begin a TS-expression, and
     thus might be involved in the decision about reducing an application: *)

  IDENTIFIER Wunderscore Wlparen Kumax CONSTANT_SEMI CONSTANT Klambda
  KSigma KPi VARIABLE

%nonassoc

  (* We want [f x y] to reduce to [(f x) y] *)

  Reduce_application

%%

lf_type:
| t=unmarked_lf_type
    { Position($startpos, $endpos), t}
| Wlparen t=lf_type Wrparen 
    { t }

unmarked_lf_type:
| f=lf_type_constant args=list(lf_expr)
    { F_APPLY(f,args) }
| KPi v=variable Colon a=lf_type Wcomma b=lf_type
    %prec Reduce_binder
    { F_Pi(v,a,b) }
| KSigma v=variable Colon a=lf_type Wcomma b=lf_type
    %prec Reduce_binder
    { F_Sigma(v,a,b) }
| Wlparen v=variable Colon a=lf_type Wrparen Wtimes b=lf_type
    { F_Sigma(v,a,b) }
| a=lf_type Wtimes b=lf_type
    { F_Sigma(newunused(),a,b) }
| Wlparen v=variable Colon a=lf_type Wrparen Wstar b=lf_type
    { F_Sigma(v,a,b) }
| a=lf_type Wstar b=lf_type
    { F_Sigma(newunused(),a,b) }
| Wlparen v=variable Colon a=lf_type Wrparen Arrow b=lf_type
   { F_Pi(v,a,b) }
| a=lf_type Arrow b=lf_type
   { F_Pi(newunused(),a,b) }
| Singleton Wlparen x=lf_expr Colon t=lf_type Wrparen
    { F_Singleton(x,t) }
| Wlbracket a=lf_expr Type Wrbracket
    { F_APPLY(F_istype, [a]) }
| Wlbracket a=lf_expr Colon b=lf_expr Wrbracket
    { F_APPLY(F_hastype, [a;b]) }
| Wlbracket a=lf_expr Wequal b=lf_expr Colon c=lf_expr Wrbracket
    { F_APPLY(F_object_equality, [a;b;c]) }
| Wlbracket a=lf_expr Wequal b=lf_expr Wrbracket
    { F_APPLY(F_type_equality, [a;b]) }

| Wlbracket a=lf_expr Wtilde b=lf_expr Colon Type Wrbracket
    { F_APPLY(F_type_uequality, [a;b]) }
| Wlbracket a=lf_expr Wtilde b=lf_expr Wrbracket
    { F_APPLY(F_object_uequality, [a;b]) }

lf_type_constant:
| l=IDENTIFIER 
    { 
      try List.assoc l Names.string_to_type_constant
      with 
        Not_found ->
          Printf.fprintf stderr "%s: unknown type constant %s\n" 
            (errfmt (Position($startpos, $endpos)))
            l;
          flush stderr;
          $syntaxerror
    }

lf_expr:
| e=unmarked_lf_expr 
    {(Position($startpos, $endpos), e)}

| Wlparen Kpi1 x=lf_expr Wrparen
    { pi1 x }
| Wlparen Kpi12 x=lf_expr Wrparen
    { pi1 (pi2 x) }
| Wlparen Kpi122 x=lf_expr Wrparen
    { pi1 (pi2 (pi2 x)) }
| Wlparen Kpi1222 x=lf_expr Wrparen
    { pi1 (pi2 (pi2 (pi2 x))) }

| Wlparen Kpi2 x=lf_expr Wrparen
    { pi2 x }
| Wlparen Kpi22 x=lf_expr Wrparen
    { pi2 (pi2 x) }
| Wlparen Kpi222 x=lf_expr Wrparen
    { pi2 (pi2 (pi2 x)) }
| Wlparen Kpi2222 x=lf_expr Wrparen
    { pi2 (pi2 (pi2 (pi2 x))) }

unmarked_lf_expr:
| e=unmarked_atomic_term
    { e  }
| e=lf_lambda_expression
    { e }
| Wlparen Kpair a=lf_expr b=lf_expr Wrparen
    { CONS(a, b) }

lf_lambda_expression:
| Wlparen Klambda v= variable_or_unused Wcomma body=lf_expr Wrparen
    { let (v,body) = Substitute.subst_fresh (v,body) in LAMBDA(v,body) }
| Wlparen v= variable_or_unused ArrowFromBar body=lf_lambda_expression_body Wrparen
    { let (v,body) = Substitute.subst_fresh (v,body) in LAMBDA(v,body) }

lf_lambda_expression_body:
| e=lf_expr
    { e }
| v= variable_or_unused ArrowFromBar body=lf_lambda_expression_body
    { Position($startpos, $endpos), let (v,body) = Substitute.subst_fresh (v,body) in LAMBDA(v,body) }

unmarked_atomic_term:
| variable
    { EVAL(V $1,END) }
| empty_hole {$1}
| tac= tactic_expr
    { cite_tactic tac END }
| Wlparen f=lf_expr_head args=list(lf_expr) Wrparen
    { EVAL(f,list_to_spine args) }

lf_expr_head:
| tsterm_head
    { $1 }
| variable
    { V $1 }
| tac= tactic_expr
    { TAC tac }

tactic_expr:
| Wdollar name=IDENTIFIER
    { Tactic_name name }
| Wdollar index=NUMBER
    { Tactic_index index }

command: c=command0 
  { Position($startpos, $endpos), c }

command0:
| Weof
    { raise Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Colon Type Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Colon KUlevel eqns=preceded(Semicolon,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }

| WRule num=separated_nonempty_list(Wperiod,NUMBER) name=IDENTIFIER DoubleColon t=lf_type Wperiod
    { Toplevel.Rule (num,name,t) }

| WRule num=separated_nonempty_list(Wperiod,NUMBER) name=IDENTIFIER Colon t=lf_type_from_ts_syntax Wperiod
    { Toplevel.Rule (num,name,t) }

| Axiom v=IDENTIFIER Colon t=ts_expr Wperiod
    { Toplevel.AxiomTS(v,t) }

| Axiom LF v=IDENTIFIER Colon t=lf_type Wperiod
    { Toplevel.AxiomLF(v,t) }

| Axiom LFtypeTS v=IDENTIFIER Colon t=lf_type_from_ts_syntax Wperiod
    { Toplevel.AxiomLF(v,t) }

| WCheck TS o=ts_expr Wperiod
    { Toplevel.CheckTS o }

| WCheck LF e=lf_expr Wperiod
    { Toplevel.CheckLF e }

| WCheck LFtype e=lf_type Wperiod
    { Toplevel.CheckLFtype e }

| WCheck LFtypeTS e= lf_type_from_ts_syntax Wperiod
    { Toplevel.CheckLFtype e }

| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }

| WAlpha e1=ts_expr Wequal e2=ts_expr Wperiod
    { Toplevel.Alpha (e1, e2) }

| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Semicolon d1=ts_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Wperiod 
    { Toplevel.ODefinition (name, parms, o, t, None) }

| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr Semicolon d1=ts_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, Some d1) }
| WDefine name=IDENTIFIER parms=parmList Colonequal t=ts_expr Wperiod 
    { Toplevel.TDefinition (name, parms, t, None) }

| WDefine name=IDENTIFIER parms=parmList Colonequal t1=ts_expr Wequal t2=ts_expr Wperiod 
    { Toplevel.TeqDefinition (name, parms, t1, t2) }

| WDefine name=IDENTIFIER parms=parmList Colonequal o1=ts_expr Wequal o2=ts_expr Colon t=ts_expr Wperiod 
    { Toplevel.OeqDefinition (name, parms, o1, o2, t) }

| WShow Wperiod 
    { Toplevel.Show None }
| WShow n=NUMBER Wperiod 
    { Toplevel.Show (Some n) }
| WEnd Wperiod
    { Toplevel.End }

uParm: vars=nonempty_list(IDENTIFIER) Colon KUlevel eqns=preceded(Semicolon,uEquation)*
    { UParm (UContext ((List.map make_Var vars),eqns)) }
tParm: vars=nonempty_list(IDENTIFIER) Colon Type 
    { TParm (List.map make_Var vars) }
oParm: vars=nonempty_list(IDENTIFIER) Colon t=ts_expr 
    { OParm (List.map (fun s -> (Var s,t)) vars) }

uEquation:
| u=ts_expr Wequal v=ts_expr 
    { (u,v) }
| v=ts_expr Wgreaterequal u=ts_expr 
    { let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }
| u=ts_expr Wlessequal v=ts_expr 
    { let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }
| v=ts_expr Wgreater u=ts_expr 
    { let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }
| u=ts_expr Wless v=ts_expr 
    { let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

parenthesized(X): x=delimited(Wlparen,X,Wrparen) {x}
list_of_parenthesized(X): list(parenthesized(X)) {$1}
parmList: list_of_parenthesized(parm) {$1}
parm:
| uParm { $1 } 
| tParm { $1 }
| oParm { $1 } 

ts_exprEof: a=ts_expr Weof {a}

lf_type_from_ts_syntax:
| Wlparen t= lf_type_from_ts_syntax Wrparen 
    { t }
| unmarked_lf_type_from_ts_syntax
    { Position($startpos, $endpos), $1 }

unmarked_lf_type_from_ts_syntax:
| f=lf_type_constant
    { F_APPLY(f,[]) }
| Wlparen v=variable Colon a= lf_type_from_ts_syntax Wrparen DoubleArrow b= lf_type_from_ts_syntax
   { F_Pi(v,a,b) }
| a= lf_type_from_ts_syntax DoubleArrow b= lf_type_from_ts_syntax
   { F_Pi(newunused(),a,b) }

(* judgments *)
| Wlbracket x= lf_expr_from_ts_syntax Wequal y= lf_expr_from_ts_syntax Colon t= lf_expr_from_ts_syntax Wrbracket
    { unmark (object_equality x y t) }

(* introduction of parameters *)
| Wlbracket 
    separated_list(Wcomma,separated_pair(variable,Colon,lf_expr_from_ts_syntax))
    Turnstile v= variable Type Wrbracket
    DoubleArrow u= lf_type_from_ts_syntax
    { add_sigma (Position($startpos, $endpos)) v texp istype u }
| Wlbracket 
    separated_list(Wcomma,separated_pair(variable,Colon,lf_expr_from_ts_syntax))
    Turnstile v= variable Colon t= lf_expr_from_ts_syntax Wrbracket
    DoubleArrow u= lf_type_from_ts_syntax
    { add_sigma (Position($startpos, $endpos)) v oexp (fun o -> hastype o t) u }

lf_expr_from_ts_syntax:
| arg= lf_expr_from_ts_syntax Backslash f= lf_expr_from_ts_syntax
    { Position($startpos, $endpos), APPLY(f, arg) }
| tac= tactic_expr
    { (Position($startpos, $endpos), cite_tactic tac END) }
| e = ts_expr
    { e }
| v= variable_or_unused DoubleArrowFromBar body=lf_expr_from_ts_syntax
    { Position($startpos, $endpos), let (v,body) = Substitute.subst_fresh (v,body) in LAMBDA(v,body) }
| o=lf_expr_from_ts_syntax DoubleBackslash f=lf_expr_from_ts_syntax
    { Position($startpos, $endpos), APPLY(f, o) }

ts_expr:
| unmarked_ts_expr
    { (Position($startpos, $endpos), $1) }
| parenthesized(ts_expr) 
    {$1}

tsterm_head:
| name=CONSTANT
    { try List.assoc name Names.lf_expr_head_strings with Not_found -> V (Var name) }

arglist:
| Wlparen a=separated_list(Wcomma,lf_expr_from_ts_syntax) Wrparen
    {a}

(* it's tempting to include '_' (Wunderscore) as a variable but there would be an 
    ambiguity when looking at the start [ _ |-> x ] and [ _ ].  In the first case,
   it's an unused variable, and in the second case, it's an empty hole. *)

empty_hole: Wunderscore { new_hole () }
unused_variable: Wunderscore { newunused() }
variable_or_unused: variable {$1} | unused_variable {$1}

variable:
| IDENTIFIER { Var $1 }
| v=VARIABLE { v }

unmarked_ts_expr:
| variable
    { EVAL(V $1,END) }
| empty_hole {$1}
| f=ts_expr o=ts_expr
    %prec Reduce_application
    { let pos = Position($startpos, $endpos) in 
      EVAL(O O_ev, f ** o ** (pos, cite_tactic (Tactic_name "ev3") END) ** END) }
| Klambda x=variable Colon t=ts_expr Wcomma o=ts_expr
    %prec Reduce_binder
    { make_O_lambda t (x,o) }
| Wstar o=ts_expr
    %prec Reduce_star
    { make_T_El o }
| KPi x=variable Colon t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_T_Pi t1 (x,t2) }
| Wlparen x=variable Colon t=ts_expr Wrparen Arrow u=ts_expr
    { make_T_Pi t (x,u) }
| t=ts_expr Arrow u=ts_expr
    { make_T_Pi t (newunused(),u) }
| KSigma x=variable Colon t1=ts_expr Wcomma t2=ts_expr
    %prec Reduce_binder
    { make_T_Sigma t1 (x,t2) }
| Kumax Wlparen u=ts_expr Wcomma v=ts_expr Wrparen
    { EVAL(U U_max, u**v**END)  }
| label=tsterm_head args=arglist
    {
     let args = list_to_spine args in
     match label with
     | V _ -> EVAL(label,args)
     | _ -> (
         match head_to_vardist label with
         | None -> EVAL(label,args)
         | Some (n,_) ->
             if n = 0 then EVAL(label,args)
             else
               raise (MarkedError
                        ( Position($startpos, $endpos),
                          "expected " ^ string_of_int n ^ " variable" ^ if n != 1 then "s" else "")))
   }
| name=CONSTANT_SEMI vars=separated_list(Wcomma,variable_or_unused) Wrbracket args=arglist
    {
     let label = 
       try List.assoc name Names.lf_expr_head_strings
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
                      "expected " ^ string_of_int nvars ^ " variable" ^ if nvars != 1 then "s" else ""));
         let nargs = List.length varindices
         in
         if List.length args != nargs then
           raise (MarkedError
                    ( Position($startpos, $endpos),
                      "expected " ^ string_of_int nargs ^ " argument" ^ if nargs != 1 then "s" else ""));
         let args = List.map2 (
           fun indices arg ->
             (* example: indices = [0;1], change arg to (LAMBDA v_0, (LAMBDA v_1, arg)) *)
             List.fold_right (
             fun index arg -> with_pos (get_pos arg) (
	       let v = List.nth vars index in
	       let (v,arg) = Substitute.subst_fresh (v,arg) in 
	       LAMBDA(v,arg))
            ) indices arg
          ) varindices args
         in
         EVAL(label,list_to_spine args)
   }
 
(* 
  Local Variables:
  compile-command: "make grammar.cmo "
  End:
 *)

