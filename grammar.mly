%{ 
open Error
open Variables
open Typesystem
open Names
open Helpers
open Definitions

let add_single v t u = F_Pi(v, t, u)

let add_definition e t =
  let v = newfresh (Var "e") in
  F_Sigma(v, with_pos_of e (F_Singleton(e,oexp)), hastype (var_to_lf v) t)

let car (hd,reversed_args) = (hd, CAR reversed_args)

let cdr (hd,reversed_args) = (hd, CDR reversed_args)

let app (hd,reversed_args) arg = (hd, ARG(arg,reversed_args))

let fix1 pos v t = Substitute.subst_type (v,pi1 (var_to_lf_pos pos v)) t

let apply_binder pos (c:(var marked * lf_expr) list) v t1 t2 u = 
  let (vpos,v) = v in
  let u = fix1 vpos v u in
  let w = newfresh v in
  let ww = var_to_lf_pos vpos w in
  let t1 = List.fold_left (fun t1 (_,t) -> with_pos vpos (unmark (oexp @-> t1))) t1 c in
  let ww = List.fold_left 
      (fun ww (x,t) -> 
	let (xpos,x) = x in 
	Substitute.apply_args ww (ARG(var_to_lf (*pos*) x,END)))
      ww c in
  let t2 = new_pos pos (t2 ww) in
  let t2 = List.fold_right (
    fun (x,t) t2 -> 
      let (xpos,x) = x in 
      let x' = newunused() in
      with_pos pos (F_Pi(x, oexp, with_pos pos (F_Pi(x', hastype (var_to_lf (*pos*) x) t, t2))))
   ) c t2 in
  F_Pi(v, (pos, F_Sigma(w, t1, t2)), u)

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

  Wlparen Wrparen Wrbracket Wlbracket Wcomma Wperiod Colon Wstar
  Arrow ArrowFromBar Wequal Colonequal Wunderscore WRule Wgreaterequal Wgreater
  Wlessequal Wless Semicolon Ulevel Kumax Type KPi Klambda KSigma WCheck
  Definition WShow WEnd WVariable WAlpha Weof WCheckUniverses Wtilde Singleton
  Axiom Wdollar LF TS Kpair K_1 K_2 Wtimes Slash Turnstile DoubleArrow
  DoubleColon DoubleArrowFromBar DoubleSemicolon Theorem Wlbrace Wrbrace

(* precedences, lowest first *)

%right

  (* we want [lambda x, lambda y, b] to be [lambda x, (lambda y, b)] *)
  (* we want [lambda x, f b] to be [lambda x, (f b)] *)
  Reduce_binder

%right

  (* function type *)
  (* we want [a -> b -> c] to be [a -> (b -> c)] *)

  DoubleArrowFromBar
  DoubleArrow
  Arrow

%nonassoc

  (* we want  [*f x] to be [*(f x)]  and  [*x->y] to be [( *x )->y]  *)
  Reduce_star
  Wstar

%right

  (* product type *)
  (** we want [a ** b ** c] to be [a ** (b ** c)], by analogy with [a -> b] **)
  (** we want [a ** b -> c] to be [(a ** b) -> c] **)

  Wtimes

%left

  (* substitution *)
  (* we want [f/x/y] to be [(f/x)/y] *)

  Slash

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
| a=lf_type Wtimes b=lf_type
    { F_Sigma(newunused(),a,b) }
| Wlparen v=variable Colon a=lf_type Wrparen Wtimes b=lf_type
    { F_Sigma(v,a,b) }
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

| Wlbracket a=lf_expr Wtilde b=lf_expr Type Wrbracket
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

unmarked_lf_expr:
| e=unmarked_atomic_term
    { e  }
| e=lf_lambda_expression
    { e }
| Wlparen Kpair a=lf_expr b=lf_expr Wrparen
    { CONS(a, b) }

lf_lambda_expression:
| Wlparen Klambda v= marked_variable_or_unused Wcomma body=lf_expr Wrparen
    { 
      let (pos,v) = v in
      let (v,body) = Substitute.subst_fresh pos (v,body) in 
      LAMBDA(v,body) }

| Wlparen v= marked_variable_or_unused ArrowFromBar body= lf_lambda_expression_body Wrparen
    { 
      let (pos,v) = v in
      let (v,body) = Substitute.subst_fresh pos (v,body) in 
      LAMBDA(v,body) }

lf_lambda_expression_body:
| e=lf_expr
    { e }
| v= marked_variable_or_unused ArrowFromBar body=lf_lambda_expression_body
    { Position($startpos, $endpos), 
      let (pos,v) = v in
      let (v,body) = Substitute.subst_fresh pos (v,body) in 
      LAMBDA(v,body) }

unmarked_atomic_term:
| empty_hole {$1}
| hd_args= lf_expr_head
    {let (hd,args) = hd_args in
     let args = reverse_spine args in
     APPLY(hd,args) }
| Wlparen hd_args= lf_expr_head_and_reversed_spine Wrparen
    {let (hd,args) = hd_args in
     let args = reverse_spine args in
     APPLY(hd,args) }

lf_expr_head:
| tsterm_head
    { $1, END }
| variable
    { V $1, END }
| tac= tactic_expr
    { TAC tac, END }
| hd_args=lf_expr_head K_1
    { car hd_args }
| hd_args=lf_expr_head K_2
    { cdr hd_args }
| Wlparen hd_args=lf_expr_head_and_reversed_spine Wrparen K_1
    { car hd_args }
| Wlparen hd_args=lf_expr_head_and_reversed_spine Wrparen K_2
    { cdr hd_args }

lf_expr_head_and_reversed_spine:
| lf_expr_head {$1}
| hd_args=lf_expr_head_and_reversed_spine arg=lf_expr
    { app hd_args arg }

tactic_expr:
| Wdollar name=IDENTIFIER
    { Tactic_name name }
| Wdollar index=NUMBER
    { Tactic_index index }

command: c=command0 
  { Position($startpos, $endpos), c }

dotted_number: n=separated_nonempty_list(Wperiod,NUMBER) {n}

command0:
| Weof
    { raise Eof }
| WVariable vars=nonempty_list(IDENTIFIER) Type Wperiod
    { Toplevel.Variable vars }
| WVariable vars=nonempty_list(IDENTIFIER) Ulevel eqns=preceded(Semicolon,uEquation)* Wperiod
    { Toplevel.UVariable (vars,eqns) }

| WRule num= dotted_number name=IDENTIFIER DoubleColon t=lf_type Wperiod
    { Toplevel.Rule (num,name,t) }

| WRule num= dotted_number name=IDENTIFIER t=lf_type_from_ts_syntax Wperiod
    { Toplevel.Rule (num,name,t) }

| Axiom v=IDENTIFIER Colon t=ts_expr Wperiod
    { Toplevel.AxiomTS(v,t) }

| Axiom LF v=IDENTIFIER Colon t=lf_type Wperiod
    { Toplevel.AxiomLF(v,t) }

| WCheck TS o=ts_expr Wperiod
    { Toplevel.CheckTS o }

| WCheck LF e=lf_expr Wperiod
    { Toplevel.CheckLF e }

| WCheck Colon e= lf_type_from_ts_syntax Wperiod
    { Toplevel.CheckLFtype e }

| WCheck DoubleColon e=lf_type Wperiod
    { Toplevel.CheckLFtype e }

| WCheckUniverses Wperiod
    { Toplevel.CheckUniverses }

| WAlpha e1=ts_expr Wequal e2=ts_expr Wperiod
    { Toplevel.Alpha (e1, e2) }

| Definition name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.ODefinition (pos,name, parms, o, t, Some d1) }
| Definition name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Semicolon d1=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.ODefinition (pos,name, parms, o, t, Some d1) }
| Definition name=IDENTIFIER parms=parmList Colonequal o=ts_expr Colon t=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.ODefinition (pos,name, parms, o, t, None) }

| Theorem name=IDENTIFIER parms=parmList Colon t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.Theorem (pos,name, parms, t, Some d1) }
| Theorem name=IDENTIFIER parms=parmList Colon t=ts_expr Semicolon d1=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.Theorem (pos,name, parms, t, Some d1) }
| Theorem name=IDENTIFIER parms=parmList Colon t=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.Theorem (pos,name, parms, t, None) }

| Definition name=IDENTIFIER parms=parmList Colonequal t=ts_expr DoubleSemicolon d1=lf_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.TDefinition (pos,name, parms, t, Some d1) }
| Definition name=IDENTIFIER parms=parmList Colonequal t=ts_expr Semicolon d1=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.TDefinition (pos,name, parms, t, Some d1) }
| Definition name=IDENTIFIER parms=parmList Colonequal t=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.TDefinition (pos,name, parms, t, None) }

| Definition name=IDENTIFIER parms=parmList Colonequal t1=ts_expr Wequal t2=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.TeqDefinition (pos,name, parms, t1, t2) }

| Definition name=IDENTIFIER parms=parmList Colonequal o1=ts_expr Wequal o2=ts_expr Colon t=ts_expr Wperiod 
    { 
      let pos = Position($startpos, $endpos) in
      Toplevel.OeqDefinition (pos,name, parms, o1, o2, t) }

| WShow Wperiod 
    { Toplevel.Show None }
| WShow n=NUMBER Wperiod 
    { Toplevel.Show (Some n) }
| WEnd Wperiod
    { Toplevel.End }

marked_variable:
| IDENTIFIER
    { Position($startpos, $endpos), Var $1 }

uParm: vars=nonempty_list(marked_variable) Ulevel eqns=preceded(Semicolon,marked_uEquation)*
    { UParm (UContext (vars,eqns)) }

tParm: vars=nonempty_list(marked_variable) Type 
    { TParm vars }

oParm: vars=nonempty_list(marked_variable) Colon t=ts_expr 
    { OParm (List.map (fun s -> (s,t)) vars) }

marked_uEquation:
| uEquation
    { Position($startpos, $endpos), $1 }

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
| Wlparen t= unmarked_lf_type_from_ts_syntax Wrparen
    { Position($startpos, $endpos), t }
| t= unmarked_lf_type_from_ts_syntax
    { Position($startpos, $endpos), t }

unmarked_lf_type_from_ts_syntax:
| f=lf_type_constant
    { F_APPLY(f,[]) }

| Wlparen v=variable Colon a= lf_type_from_ts_syntax Wrparen DoubleArrow b= lf_type_from_ts_syntax
    { F_Pi(v,a,b) }

| a= lf_type_from_ts_syntax DoubleArrow b= lf_type_from_ts_syntax
    { F_Pi(newunused(),a,b) }

| Wlparen v=variable Colon a= lf_type_from_ts_syntax Wrparen Wtimes b= lf_type_from_ts_syntax
    { F_Sigma(v,a,b) }

| a= lf_type_from_ts_syntax Wtimes b= lf_type_from_ts_syntax
    { F_Sigma(newunused(),a,b) }

(* judgments *)

| Turnstile x= lf_expr_from_ts_syntax Colon t= lf_expr_from_ts_syntax
    { add_definition x t }

| Turnstile a= lf_expr_from_ts_syntax Type
    { F_APPLY(F_istype, [a]) }

| Wlbracket a= lf_expr_from_ts_syntax Wequal b= lf_expr_from_ts_syntax Wrbracket
    { F_APPLY(F_type_equality, [a;b]) }

| Wlbracket x= lf_expr_from_ts_syntax Colon t= lf_expr_from_ts_syntax Wrbracket
    { unmark (hastype x t) }

| Wlbracket x= lf_expr_from_ts_syntax Wequal y= lf_expr_from_ts_syntax Colon t= lf_expr_from_ts_syntax Wrbracket
    { unmark (object_equality x y t) }

| Wlbracket a= lf_expr_from_ts_syntax Wtilde b= lf_expr_from_ts_syntax Type Wrbracket
    { F_APPLY(F_type_uequality, [a;b]) }

| Wlbracket a= lf_expr_from_ts_syntax Wtilde b= lf_expr_from_ts_syntax Wrbracket
    { F_APPLY(F_object_uequality, [a;b]) }

(* introduction of parameters *)

| Wlbrace c= context v= variable Ulevel Wrbrace u= lf_type_from_ts_syntax
    %prec Reduce_binder
    { if c <> [] then $syntaxerror; add_single v uexp u }

| Wlbrace c= context v= marked_variable Type Wrbrace u= lf_type_from_ts_syntax
    %prec Reduce_binder
    { let pos = Position($startpos, $endpos) in apply_binder pos c v texp istype u }

| Wlbrace c= context v= marked_variable Colon t= lf_expr_from_ts_syntax Wrbrace u= lf_type_from_ts_syntax
    %prec Reduce_binder
    { let pos = Position($startpos, $endpos) in apply_binder pos c v oexp (fun o -> hastype o t) u }

context:
| c= terminated( separated_list(
		      Wcomma,
		      separated_pair(
		           marked_variable_or_unused, 
		           Colon,
		           lf_expr_from_ts_syntax)),
		 Turnstile)
    {c}

lf_expr_from_ts_syntax:

| f=lf_expr_from_ts_syntax Slash o=lf_expr_from_ts_syntax
    { Substitute.apply_args f (o ** END) }

| tac= tactic_expr
    { (Position($startpos, $endpos), cite_tactic tac END) }

| e = ts_expr
    { e }

| v= marked_variable_or_unused DoubleArrowFromBar body=lf_expr_from_ts_syntax
    { Position($startpos, $endpos), 
      let (pos,v) = v in
      let (v,body) = Substitute.subst_fresh pos (v,body) in 
      LAMBDA(v,body) }
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

empty_hole: Wunderscore { cite_tactic (Tactic_name "default") END }

unused_variable: Wunderscore { newunused() }

variable_or_unused: variable {$1} | unused_variable {$1}

marked_variable_or_unused: variable_or_unused { Position($startpos, $endpos), $1 }

variable:
| IDENTIFIER { Var $1 }
| v=VARIABLE { v }

unmarked_ts_expr:
| variable
    { APPLY(V $1,END) }
| empty_hole {$1}
| f=ts_expr o=ts_expr
    %prec Reduce_application
    { let pos = Position($startpos, $endpos) in 
      APPLY(O O_ev, f ** o ** (pos, cite_tactic (Tactic_name "ev3") END) ** END) }
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
    { APPLY(U U_max, u**v**END)  }
| label=tsterm_head args=arglist
    { APPLY(label,list_to_spine args) }
| name=CONSTANT_SEMI vars=separated_list(Wcomma,marked_variable_or_unused) Wrbracket args=arglist
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
	       let (pos,v) = List.nth vars index in
	       let (v,arg) = Substitute.subst_fresh pos (v,arg) in 
	       LAMBDA(v,arg))
            ) indices arg
          ) varindices args
         in
         APPLY(label,list_to_spine args)
   }
 
(* 
  Local Variables:
  compile-command: "make grammar.cmo "
  End:
 *)

