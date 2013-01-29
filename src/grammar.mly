%{
open Error
open Variables
open Typesystem
open Names
open Helpers
open Parse
open Printf
open Printer
%}
%start command ts_exprEof
%type <Toplevel.command> command
%type <Typesystem.lf_type> lf_type ts_judgment
%type <Typesystem.lf_expr> lf_expr ts_expr

(* for parsing a single expression *)
%type <Typesystem.lf_expr> ts_exprEof

%token <int> NUMBER
%token <string> IDENTIFIER CONSTANT CONSTANT_SEMI STRING
%token <Variables.var> VARIABLE
%token

  (* tokens *)

  LeftParen RightParen RightBracket LeftBracket Comma Period Colon Star Arrow
  ArrowFromBar Equal Underscore Axiom GreaterEqual Greater LessEqual Less
  Semicolon Ulevel Kumax Type Pi Lambda Sigma Check Show End Variable Alpha EOF
  Universes Tilde Singleton Dollar LF TS Kpair K_1 K_2 K_CAR K_CDR Times
  Turnstile DoubleArrow DoubleArrowFromBar ColonColonEqual ColonEqual Theorem
  LeftBrace RightBrace TurnstileDouble ColonColon Include Clear EqualEqual
  Witness K_wd_underscore

(* precedences, lowest first *)

%right

  Reduce_binder

%right

  Turnstile
  TurnstileDouble

%right

  DoubleArrowFromBar			(* TS notation for LF lambda *)
  DoubleArrow				(* function type *)
  Arrow					(* function type *)
  Times					(* product type *)

%nonassoc

  Star					(* *x denotes @[El][x] *)

%nonassoc

  Equal

%left

  LeftBracket				(* f[a] denotes substitution *)

%right

  (* These are the tokens that can begin a TS-expression, and
     thus might be involved in the decision about reducing an application: *)

  IDENTIFIER Underscore LeftParen Kumax CONSTANT_SEMI CONSTANT Lambda
  Sigma Pi VARIABLE Dollar K_wd_underscore

%nonassoc

  Reduce_application

  (* We want [f -> (f,END) -> (f)] unless there is another expr coming. *)

  (* In LF mode, we want [f x y z -> (f,x::END) y z -> (f,(y::x::END)) -> (f,(z::y::x::END)) -> (f x y z)] *)

%left

  K_1 K_2

%%

lf_type:

    | t= unmarked_lf_type
	{ Position($startpos, $endpos), t}

    | LeftParen t= lf_type RightParen 
	{ t }

unmarked_lf_type:

    | f= lf_type_constant args= lf_expr*
	{ F_Apply(f,args) }

    | Pi v= variable Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
	{ F_Pi(v,a,b) }

    | Sigma v= variable Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
    | LeftParen v= variable Colon a= lf_type RightParen Times b= lf_type
	{ F_Sigma(v,a,b) }

    | a= lf_type Times b= lf_type
	{ F_Sigma(newunused(),a,b) }

    | LeftParen v= variable Colon a= lf_type RightParen Arrow b= lf_type
       { F_Pi(v,a,b) }

    | a= lf_type Arrow b= lf_type
       { unmark (a @-> b) }

    | Singleton LeftParen x= lf_expr Colon t= lf_type RightParen
	{ F_Singleton(x,t) }

    | LeftBracket t= lf_expr Type RightBracket
	{ unmark (istype t) }

    | LeftBracket a= lf_expr Colon t= lf_expr RightBracket
	{ unmark (hastype a t) }

    | LeftBracket a= lf_expr EqualEqual b= lf_expr Colon t= lf_expr RightBracket
	{ unmark (object_equality a b t) }

    | LeftBracket t= lf_expr EqualEqual u= lf_expr RightBracket
	{ unmark (type_equality t u) }

    | LeftBracket t= lf_expr Tilde u= lf_expr Type RightBracket
	{ unmark (type_uequality t u) }

    | LeftBracket a= lf_expr Tilde b= lf_expr Colon t= lf_expr RightBracket
	{ unmark (object_uequality a b t) }

    | a= lf_type Turnstile b= lf_type
    	{ let v = good_var_name a (Var "foo") in (* the "|-" operator is not fully implemented yet *)
	  let v = get_pos a, v in
	  unmark (pi1_implication (v,a) b) }

    | v= marked_variable Type
	{ let (pos,v) = v in F_Sigma(v,texp,istype (var_to_lf_pos pos v)) }

    | v= marked_variable ColonColon t= lf_expr
	{ let (pos,v) = v in F_Sigma(v,oexp,hastype (var_to_lf_pos pos v) t) }

    | v= marked_variable ColonColonEqual e= lf_expr ColonColon t= lf_expr
	{ let (pos,v) = v in F_Sigma(v,with_pos_of e (F_Singleton(e,oexp)),hastype (var_to_lf_pos pos v) t) }

lf_type_constant:

    | l= IDENTIFIER 
	{ let pos = Position($startpos, $endpos) in try lookup_type_constant pos l with Not_found -> $syntaxerror }

lf_expr:

    | e= unmarked_lf_expr 
	{(Position($startpos, $endpos), e)}

    | e= parenthesized(lf_expr) {e}

unmarked_lf_expr:

    | LeftParen Kpair a= lf_expr b= lf_expr RightParen
    | LeftParen a= lf_expr Comma b= lf_expr RightParen
	{ CONS(a, b) }

    | Lambda v= marked_variable_or_unused Comma body= lf_expr
    | v= marked_variable_or_unused ArrowFromBar body= lf_expr
	{ 
	  let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | empty_hole 
	{$1}

    | head_and_args = short_head_and_reversed_spine
    | LeftParen head_and_args= lf_expr_head_and_reversed_spine RightParen
	{ let (hd,args) = head_and_args in APPLY(hd,reverse_spine args) }

lf_expr_head_and_reversed_spine:

    | head_and_args= lf_expr_head_and_reversed_spine arg= lf_expr
    | head_and_args= short_head_and_reversed_spine arg= lf_expr
	{ app head_and_args arg }

    | head_and_args= lf_expr_head_and_reversed_spine K_CAR
    | head_and_args= short_head_and_reversed_spine K_CAR
	{ car head_and_args }

    | head_and_args= lf_expr_head_and_reversed_spine K_CDR
    | head_and_args= short_head_and_reversed_spine K_CDR
	{ cdr head_and_args }

short_head_and_reversed_spine:

    | tsterm_head
	{ $1, END }

    | variable
	{ V $1, END }

    | head_and_args= short_head_and_reversed_spine K_1
    | head_and_args= parenthesized(lf_expr_head_and_reversed_spine) K_1
    	{ car head_and_args }

    | head_and_args= short_head_and_reversed_spine K_2
    | head_and_args= parenthesized(lf_expr_head_and_reversed_spine) K_2
    	{ cdr head_and_args }

    | tac= closed_tactic_expr
	{ TAC tac, END }

closed_tactic_expr:

    | Dollar LeftParen e= tactic_expr RightParen
	{ e }

    | Dollar name= IDENTIFIER
	{ Tactic_name name }

    | Dollar index= NUMBER
	{ Tactic_index index }

tactic_expr:

    | s= tactic_expr_2
	{s}

    | s= tactic_expr_2 Semicolon t= tactic_expr
	{ Tactic_sequence (s,t) }

tactic_expr_2:

    | name= IDENTIFIER
	{ Tactic_name name }

dotted_number: n= separated_nonempty_list(Period,NUMBER) {n}

command: 

    | c= unmarked_command 
	{ Position($startpos, $endpos), c }

    | error Period
    | error EOF
	{ let pos = Position($startpos, $endpos) in
	  fprintf stderr "%a: syntax error\n%!" _pos pos; 
	  bump_error_count pos;
	  pos, Toplevel.SyntaxError }

    | EOF { raise Eof }

unmarked_command:

    | Variable vars= IDENTIFIER+ Type Period
	{ Toplevel.Variable vars }

    | Variable vars= IDENTIFIER+ Ulevel eqns= preceded(Semicolon,uEquation)* Period
	{ Toplevel.UVariable (vars,eqns) }

    | Axiom num= dotted_number? name= IDENTIFIER t= ts_judgment Period
	{ Toplevel.Axiom (num,name,t) }

    | Axiom LF num= dotted_number? name= IDENTIFIER Colon t= lf_type Period
	{ Toplevel.Axiom (num,name,t) }

    | Check TS? o= ts_expr Period
	{ Toplevel.CheckTS o }

    | Check LF e= lf_expr Period
	{ Toplevel.CheckLF e }

    | Check TS? Colon t= ts_judgment Period
    | Check LF Colon t= lf_type Period
	{ Toplevel.CheckLFtype t }

    | Check TS? Witness Colon t= ts_judgment Period
    | Check LF Witness Colon t= lf_type Period
	{ Toplevel.CheckWitness t }

    | Check Universes Period
	{ Toplevel.CheckUniverses }

    | Alpha e1= ts_expr EqualEqual e2= ts_expr Period
	{ Toplevel.Alpha (e1, e2) }

    | Theorem LF name= IDENTIFIER Colon thm= lf_type ColonEqual deriv= lf_expr Period 
    | Theorem name= IDENTIFIER thm= ts_judgment ColonColonEqual deriv= lf_expr Period 
    | Theorem name= IDENTIFIER thm= ts_judgment ColonEqual deriv= ts_expr Period 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Include filename= STRING Period 
	{ Toplevel.Include filename }

    | Clear Period 
	{ Toplevel.Clear }

    | Show Period 
	{ Toplevel.Show None }
    | Show n= NUMBER Period 
	{ Toplevel.Show (Some n) }

    | End Period
	{ Toplevel.End }

marked_variable:

    | IDENTIFIER
	{ Position($startpos, $endpos), Var $1 }

uEquation:

    | u= ts_expr EqualEqual v= ts_expr 
	{ (u,v) }

    | v= ts_expr GreaterEqual u= ts_expr 
    | u= ts_expr LessEqual    v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }

    | v= ts_expr Greater u= ts_expr 
    | u= ts_expr Less    v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

parenthesized(X): x= delimited(LeftParen,X,RightParen) {x}

list_of_parenthesized(X): parenthesized(X)* {$1}

ts_exprEof: a= ts_expr EOF {a}

ts_judgment:

    | LeftParen t= unmarked_ts_judgment RightParen
    | t= unmarked_ts_judgment
	{ Position($startpos, $endpos), t }

unmarked_ts_judgment:

    | f= lf_type_constant
	{ F_Apply(f,[]) }

    | LeftParen v= variable Colon a= ts_judgment RightParen DoubleArrow b= ts_judgment
	{ F_Pi(v,a,b) }

    | a= ts_judgment DoubleArrow b= ts_judgment
	{ unmark (a @-> b) }

    | LeftParen v= variable Colon a= ts_judgment RightParen Times b= ts_judgment
	{ F_Sigma(v,a,b) }

    | a= ts_judgment Times b= ts_judgment
	{ F_Sigma(newunused(),a,b) }

    | a= ts_judgment TurnstileDouble b= ts_judgment
    	{ let v = good_var_name a (Var "foo") in (* the "|-" operator is not fully implemented yet *)
	  let v = get_pos a, v in
	  unmark (pi1_implication (v,a) b) }

(* base judgments *)

    | Type
	{ let pos = Position($startpos, $endpos) in
	  let v = Var "T" in
	  F_Sigma(v, texp, with_pos pos (F_Apply(F_istype, [var_to_lf_pos pos v]))) }

    | Colon t= ts_expr
	{ let v = Var "o" in
	  let pos = get_pos t in
	  F_Sigma(v, oexp, with_pos pos (F_Apply(F_hastype, [var_to_lf_pos pos v; t]))) }

    | Turnstile x= ts_expr Colon t= ts_expr
	{ unmark (this_object_of_type (get_pos x) x t) }

    | Turnstile a= ts_expr Type
	{ let v = newfresh (Var "t") in
	  let pos = get_pos a in
	  F_Sigma(v, with_pos pos (F_Singleton(a,texp)), with_pos pos (F_Apply(F_istype, [var_to_lf_pos pos v]))) 
	}

    | j= ts_bracketed_judgment 
	{ j }

(* introduction of parameters *)

    | j= ts_bracketed_judgment u= ts_judgment
	%prec Reduce_binder
        { 
          let pos = Position($startpos, $endpos) in
          let jpos = Position($startpos(j), $endpos(j)) in
	  let w = apply_judgment_binder pos (with_pos jpos j) u in
	  unmark w
        }

    | LeftBrace c= context vbj= separated_nonempty_list(Comma,pair(marked_variable+,binder_judgment)) RightBrace u= ts_judgment
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

ts_bracketed_judgment:

    | LeftBracket a= ts_expr Type RightBracket
	{ unmark (istype a) }

    | LeftBracket a= ts_expr EqualEqual b= ts_expr RightBracket
	{ unmark (type_equality a b) }

    | LeftBracket x= ts_expr Colon t= ts_expr RightBracket
	{ unmark (hastype x t) }

    | LeftBracket x= ts_expr EqualEqual y= ts_expr Colon t= ts_expr RightBracket
	{ unmark (object_equality x y t) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Ulevel RightBracket
	{ unmark (ulevel_equality a b) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Type RightBracket
	{ unmark (type_uequality a b) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Colon t= ts_expr RightBracket
	{ unmark (object_uequality a b t) } 

    | LeftBracket p= ts_expr Colon a= ts_expr EqualEqual b= ts_expr RightBracket
	{ unmark (witnessed_type_equality p a b) }

    | LeftBracket p= ts_expr Colon x= ts_expr Colon t= ts_expr RightBracket
	{ unmark (witnessed_hastype p x t) }

    | LeftBracket p= ts_expr Colon x= ts_expr EqualEqual y= ts_expr Colon t= ts_expr RightBracket
	{ unmark (witnessed_object_equality p x y t) }

binder_judgment:

    | Ulevel { ULEV }

    | Type { IST }

    | Colon t= ts_expr { HAST t }

context:

    | c= terminated( separated_list( Comma,
			  separated_pair(
			       marked_variable_or_unused,
			       Colon, ts_expr)),
		     Turnstile)
	{c}

tsterm_head:

    | name= CONSTANT
	{ let pos = Position($startpos, $endpos) in try lookup_label pos name with Not_found -> $syntaxerror }

arglist:

    | LeftBracket a= separated_list(Comma,ts_expr) RightBracket
	{a}

empty_hole: Underscore { cite_tactic (Tactic_name "default") END }

unused_variable: Underscore { newunused() }

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

ts_spine_member:

    | x= ts_expr 
	{ Spine_arg x }

    | K_CAR 
	{ Spine_car }

    | K_CDR 
	{ Spine_cdr }

unmarked_ts_expr:

    | v= marked_variable_or_unused DoubleArrowFromBar body= ts_expr
	{ let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | e= ts_expr K_1
    	{ unmark ( Substitute.apply_args e (CAR END) ) }

    | e= ts_expr K_2
    	{ unmark ( Substitute.apply_args e (CDR END) ) }

    | tac= closed_tactic_expr
	{ cite_tactic tac END }

    | f= ts_expr LeftBracket o= separated_nonempty_list(Comma,ts_spine_member) RightBracket
	{ unmark (Substitute.apply_args f (spine_member_list_to_spine o)) }

    | variable
	{ APPLY(V $1,END) }

    | empty_hole {$1}

    | f= ts_expr o= ts_expr
	%prec Reduce_application
	{ let pos = Position($startpos, $endpos) in 
	  APPLY(O O_ev, f ** o ** (pos, cite_tactic (Tactic_name "ev3") END) ** END) }

    | Lambda x= variable Colon t= ts_expr Comma o= ts_expr
	%prec Reduce_binder
	{ make_O_lambda t (x,o) }

    | Star o= ts_expr
	{ make_T_El o }

    | Pi x= variable Colon t1= ts_expr Comma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Pi t1 (x,t2) }

    | LeftParen x= variable Colon t= ts_expr RightParen Arrow u= ts_expr
	{ make_T_Pi t (x,u) }

    | x= ts_expr Equal y= ts_expr
	{ make_T_Id (with_pos_of x (cite_tactic (Tactic_name "tn12") END)) x y }

    | t= ts_expr Arrow u= ts_expr
	{ make_T_Pi t (newunused(),u) }

    | Sigma x= variable Colon t1= ts_expr Comma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Sigma t1 (x,t2) }

    | Kumax LeftParen u= ts_expr Comma v= ts_expr RightParen
	{ APPLY(U U_max, u**v**END)  }

    | label= tsterm_head args= arglist
	{ APPLY(label,list_to_spine args) }

    | LeftParen a= ts_expr Comma b= ts_expr RightParen
	{ CONS(a,b) }

    | K_wd_underscore i= NUMBER RightBracket
	{ APPLY(V (Var_wd i), END) }

    | name= CONSTANT_SEMI vars= separated_list(Comma,marked_variable_or_unused) RightBracket args= arglist
	{
	 let label = 
	   let pos = Position($startpos, $endpos) in
	   try lookup_label pos name with Not_found -> $syntaxerror
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
  compile-command: "make -C .. src/grammar.cmo "
  End:
 *)

