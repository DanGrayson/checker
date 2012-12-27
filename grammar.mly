%{ 
open Error
open Variables
open Typesystem
open Names
open Helpers
open Definitions
open Printer
open Printf

type binder_judgment = ULEV | IST | HAST of lf_expr

let add_single v t u = F_Pi(v, t, u)

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
%type <Typesystem.lf_type> lf_type ts_judgment
%type <Typesystem.lf_expr> lf_expr ts_expr

(* for parsing a single expression *)
%type <Typesystem.lf_expr> ts_exprEof

%token <int> NUMBER
%token <string> IDENTIFIER CONSTANT CONSTANT_SEMI
%token <Variables.var> VARIABLE
%token

  (* tokens *)

  Wlparen Wrparen Wrbracket Wlbracket Wcomma Wperiod Colon Star
  Arrow ArrowFromBar Wequal Wunderscore Axiom Wgreaterequal Wgreater
  Wlessequal Wless Semicolon Ulevel Kumax Type KPi Klambda KSigma Check
  WShow WEnd WVariable WAlpha Weof CheckUniverses Wtilde Singleton
  Wdollar LF TS Kpair K_1 K_2 Times Slash Turnstile DoubleArrow
  DoubleArrowFromBar ColonColonEqual ColonEqual Theorem Wlbrace Wrbrace

(* precedences, lowest first *)

%right

  Reduce_binder

%right

  DoubleArrowFromBar			(* TS notation for LF lambda *)
  DoubleArrow				(* function type *)
  Arrow					(* function type *)
  Times					(* product type *)

%nonassoc

  Star					(* [El] *)

%left

  Slash					(* substitution *)

%right

  (* These are the tokens that can begin a TS-expression, and
     thus might be involved in the decision about reducing an application: *)

  IDENTIFIER Wunderscore Wlparen Kumax CONSTANT_SEMI CONSTANT Klambda
  KSigma KPi VARIABLE Wdollar

%nonassoc

  Reduce_application

  (* We want [f -> (f,END) -> (f)] unless there is another expr coming. *)

  (* In LF mode, we want [f x y z -> (f,x::END) y z -> (f,(y::x::END)) -> (f,(z::y::x::END)) -> (f x y z)] *)

%%

lf_type:

    | t= unmarked_lf_type
	{ Position($startpos, $endpos), t}

    | Wlparen t= lf_type Wrparen 
	{ t }

unmarked_lf_type:

    | f= lf_type_constant args= list(lf_expr)
	{ F_APPLY(f,args) }

    | KPi v= variable Colon a= lf_type Wcomma b= lf_type
	%prec Reduce_binder
	{ F_Pi(v,a,b) }

    | KSigma v= variable Colon a= lf_type Wcomma b= lf_type
	%prec Reduce_binder
	{ F_Sigma(v,a,b) }

    | a= lf_type Times b= lf_type
	{ F_Sigma(newunused(),a,b) }

    | Wlparen v= variable Colon a= lf_type Wrparen Times b= lf_type
	{ F_Sigma(v,a,b) }

    | Wlparen v= variable Colon a= lf_type Wrparen Arrow b= lf_type
       { F_Pi(v,a,b) }

    | a= lf_type Arrow b= lf_type
       { unmark (a @-> b) }

    | Singleton Wlparen x= lf_expr Colon t= lf_type Wrparen
	{ F_Singleton(x,t) }

    | Wlbracket t= lf_expr Type Wrbracket
	{ unmark (istype t) }

    | Wlbracket a= lf_expr Colon t= lf_expr Wrbracket
	{ unmark (hastype a t) }

    | Wlbracket a= lf_expr Wequal b= lf_expr Colon t= lf_expr Wrbracket
	{ unmark (object_equality a b t) }

    | Wlbracket t= lf_expr Wequal u= lf_expr Wrbracket
	{ unmark (type_equality t u) }

    | Wlbracket t= lf_expr Wtilde u= lf_expr Type Wrbracket
	{ unmark (type_uequality t u) }

    | Wlbracket a= lf_expr Wtilde b= lf_expr Colon t= lf_expr Wrbracket
	{ unmark (object_uequality a b t) }

lf_type_constant:

    | l= IDENTIFIER 
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

    | e= unmarked_lf_expr 
	{(Position($startpos, $endpos), e)}

unmarked_lf_expr:

    | e= parenthesized(unmarked_lf_expr) {e}

    | Wlparen Kpair a= lf_expr b= lf_expr Wrparen
	{ CONS(a, b) }

    | Klambda v= marked_variable_or_unused Wcomma body= lf_expr
	{ 
	  let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | v= marked_variable_or_unused ArrowFromBar body= lf_expr
	{ 
	  let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | empty_hole {$1}

    | head_and_args = short_head_and_reversed_spine
	{ let (hd,args) = head_and_args in APPLY(hd,reverse_spine args) }

    | Wlparen head_and_args= lf_expr_head_and_reversed_spine Wrparen
	{ let (hd,args) = head_and_args in APPLY(hd,reverse_spine args) }

lf_expr_head_and_reversed_spine:

    | head_and_args= lf_expr_head_and_reversed_spine arg= lf_expr
	{ app head_and_args arg }

    | head_and_args= short_head_and_reversed_spine arg= lf_expr
	{ app head_and_args arg }

short_head_and_reversed_spine:

    | tsterm_head
	{ $1, END }

    | variable
	{ V $1, END }

    | head_and_args= variable K_1	(* we need a way to write ( ... )_1 *)
    	{ car (V head_and_args, END) }

    | head_and_args= variable K_2
    	{ cdr (V head_and_args, END) }

    | tac= tactic_expr
	{ TAC tac, END }

tactic_expr:

    | Wdollar name= IDENTIFIER
	{ Tactic_name name }

    | Wdollar index= NUMBER
	{ Tactic_index index }

dotted_number: n= separated_nonempty_list(Wperiod,NUMBER) {n}

command: c= unmarked_command { Position($startpos, $endpos), c }

unmarked_command:

    | Weof
	{ trap(); raise Eof }

    | WVariable vars= nonempty_list(IDENTIFIER) Type Wperiod
	{ Toplevel.Variable vars }

    | WVariable vars= nonempty_list(IDENTIFIER) Ulevel eqns= preceded(Semicolon,uEquation)* Wperiod
	{ Toplevel.UVariable (vars,eqns) }

    | Axiom num= option(dotted_number) name= IDENTIFIER t= ts_judgment Wperiod
	{ Toplevel.Axiom (num,name,t) }

    | Axiom LF num= option(dotted_number) name= IDENTIFIER Colon t= lf_type Wperiod
	{ Toplevel.Axiom (num,name,t) }

    | Check TS o= ts_expr Wperiod
	{ Toplevel.CheckTS o }

    | Check LF e= lf_expr Wperiod
	{ Toplevel.CheckLF e }

    | Check Colon TS t= ts_judgment Wperiod
	{ Toplevel.CheckLFtype t }

    | Check Colon LF t= lf_type Wperiod
	{ Toplevel.CheckLFtype t }

    | CheckUniverses Wperiod
	{ Toplevel.CheckUniverses }

    | WAlpha e1= ts_expr Wequal e2= ts_expr Wperiod
	{ Toplevel.Alpha (e1, e2) }

    | Theorem LF name= IDENTIFIER Colon thm= lf_type ColonEqual deriv= lf_expr Wperiod 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Theorem name= IDENTIFIER thm= ts_judgment ColonColonEqual deriv= lf_expr Wperiod 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Theorem name= IDENTIFIER thm= ts_judgment ColonEqual deriv= ts_expr Wperiod 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | WShow Wperiod 
	{ Toplevel.Show None }

    | WShow n= NUMBER Wperiod 
	{ Toplevel.Show (Some n) }

    | WEnd Wperiod
	{ Toplevel.End }

marked_variable:

    | IDENTIFIER
	{ Position($startpos, $endpos), Var $1 }

uEquation:

    | u= ts_expr Wequal v= ts_expr 
	{ (u,v) }

    | v= ts_expr Wgreaterequal u= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }

    | u= ts_expr Wlessequal v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }

    | v= ts_expr Wgreater u= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

    | u= ts_expr Wless v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

parenthesized(X): x= delimited(Wlparen,X,Wrparen) {x}

list_of_parenthesized(X): list(parenthesized(X)) {$1}

ts_exprEof: a= ts_expr Weof {a}

ts_judgment:

    | Wlparen t= unmarked_ts_judgment Wrparen
	{ Position($startpos, $endpos), t }

    | t= unmarked_ts_judgment
	{ Position($startpos, $endpos), t }

unmarked_ts_judgment:

    | f= lf_type_constant
	{ F_APPLY(f,[]) }

    | Wlparen v= variable Colon a= ts_judgment Wrparen DoubleArrow b= ts_judgment
	{ F_Pi(v,a,b) }

    | a= ts_judgment DoubleArrow b= ts_judgment
	{ unmark (a @-> b) }

    | Wlparen v= variable Colon a= ts_judgment Wrparen Times b= ts_judgment
	{ F_Sigma(v,a,b) }

    | a= ts_judgment Times b= ts_judgment
	{ F_Sigma(newunused(),a,b) }

(* base judgments *)

    | Type
	{ let pos = Position($startpos, $endpos) in
	  let v = Var "t" in
	  F_Sigma(v, texp, with_pos pos (F_APPLY(F_istype, [var_to_lf_pos pos v]))) }

    | Colon t= ts_expr
	{ let v = Var "o" in
	  let pos = get_pos t in
	  F_Sigma(v, oexp, with_pos pos (F_APPLY(F_hastype, [var_to_lf_pos pos v; t]))) }

    | Turnstile x= ts_expr Colon t= ts_expr
	{ unmark (this_object_of_type (get_pos x) x t) }

    | Turnstile a= ts_expr Type
	{ let v = Var "t" in
	  let pos = get_pos a in
	  F_Sigma(v, with_pos pos (F_Singleton(a,texp)), with_pos pos (F_APPLY(F_istype, [var_to_lf_pos pos v]))) }

    | Wlbracket a= ts_expr Type Wrbracket
	{ unmark (istype a) }

    | Wlbracket a= ts_expr Wequal b= ts_expr Wrbracket
	{ unmark (type_equality a b) }

    | Wlbracket x= ts_expr Colon t= ts_expr Wrbracket
	{ unmark (hastype x t) }

    | Wlbracket x= ts_expr Wequal y= ts_expr Colon t= ts_expr Wrbracket
	{ unmark (object_equality x y t) }

    | Wlbracket a= ts_expr Wtilde b= ts_expr Ulevel Wrbracket
	{ unmark (ulevel_equality a b) }

    | Wlbracket a= ts_expr Wtilde b= ts_expr Type Wrbracket
	{ unmark (type_uequality a b) }

    | Wlbracket a= ts_expr Wtilde b= ts_expr Colon t= ts_expr Wrbracket
	{ unmark (object_uequality a b t) } 

(* introduction of parameters *)

    | Wlbrace c= context vbj= separated_nonempty_list(Wcomma,pair(nonempty_list(marked_variable),binder_judgment)) Wrbrace u= ts_judgment
	%prec Reduce_binder
	{ 
	  let pos = Position($startpos, $endpos) in
	  let r = List.fold_right 
	      (
	       fun (v,bj) u ->
		 let f = match bj with
		 | ULEV -> 
		     if c <> [] then $syntaxerror;
		     (fun v u -> with_pos_of v (add_single (unmark v) uexp u))
		 | IST -> 
		     (fun v u -> with_pos_of v (apply_binder pos c v texp istype u))
		 | HAST t -> 
		     (fun v u -> with_pos_of v (apply_binder pos c v oexp (fun o -> hastype o t) u)) in
		 List.fold_right f v u)
	      vbj u in
	  unmark r
	}

binder_judgment:

    | Ulevel { ULEV }

    | Type { IST }

    | Colon t= ts_expr { HAST t }

context:

    | c= terminated( separated_list( Wcomma,
			  separated_pair(
			       marked_variable_or_unused,
			       Colon, ts_expr)),
		     Turnstile)
	{c}

tsterm_head:

    | name= CONSTANT
	{ try List.assoc name Names.lf_expr_head_strings with Not_found -> V (Var name) }

arglist:

    | Wlparen a= separated_list(Wcomma,ts_expr) Wrparen
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

    | v= VARIABLE { v }

ts_expr:

    | e= parenthesized(ts_expr)
	{ e }

    | e= unmarked_ts_expr
	{ Position($startpos, $endpos), e }

unmarked_ts_expr:

    | v= marked_variable_or_unused DoubleArrowFromBar body= ts_expr
	{ let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | tac= tactic_expr
	{ cite_tactic tac END }

    | f= ts_expr Slash o= ts_expr
	{ unmark (Substitute.apply_args f (o ** END)) }

    | variable
	{ APPLY(V $1,END) }

    | empty_hole {$1}

    | f= ts_expr o= ts_expr
	%prec Reduce_application
	{ let pos = Position($startpos, $endpos) in 
	  APPLY(O O_ev, f ** o ** (pos, cite_tactic (Tactic_name "ev3") END) ** END) }

    | Klambda x= variable Colon t= ts_expr Wcomma o= ts_expr
	%prec Reduce_binder
	{ make_O_lambda t (x,o) }

    | Star o= ts_expr
	{ make_T_El o }

    | KPi x= variable Colon t1= ts_expr Wcomma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Pi t1 (x,t2) }

    | Wlparen x= variable Colon t= ts_expr Wrparen Arrow u= ts_expr
	{ make_T_Pi t (x,u) }

    | t= ts_expr Arrow u= ts_expr
	{ make_T_Pi t (newunused(),u) }

    | KSigma x= variable Colon t1= ts_expr Wcomma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Sigma t1 (x,t2) }

    | Kumax Wlparen u= ts_expr Wcomma v= ts_expr Wrparen
	{ APPLY(U U_max, u**v**END)  }

    | label= tsterm_head args= arglist
	{ APPLY(label,list_to_spine args) }

    | name= CONSTANT_SEMI vars= separated_list(Wcomma,marked_variable_or_unused) Wrbracket args= arglist
	{
	 let label = 
	   try List.assoc name Names.lf_expr_head_strings
	   with Not_found -> 
	     Printf.fprintf stderr "%s: unknown term constant [%s]\n%!" (errfmt (Position($startpos, $endpos))) name;
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

