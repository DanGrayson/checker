%{ 
open Error
open Variables
open Typesystem
open Names
open Helpers
open Printer
open Printf

type binder_judgment = ULEV | IST | HAST of lf_expr

let add_single v t u = F_Pi(v, t, u)

let app (hd,reversed_args) arg = (hd, ARG(arg,reversed_args))

let car (hd,reversed_args) = (hd, CAR reversed_args)

let cdr (hd,reversed_args) = (hd, CDR reversed_args)

let fix1 pos v t = Substitute.subst_type (v,pi1 (var_to_lf_pos pos v)) t

type binder = position * var * lf_type

let rec bind_pis binders b =
  match binders with
  | [] -> b
  | (pos,v,a) :: binders -> bind_pis binders (with_pos pos (F_Pi(v,a,b)))

let apply_vars f binders =
  Substitute.apply_args f (List.fold_right (fun (pos,v,a) accu -> (ARG(var_to_lf_pos pos v,accu))) binders END)

let bind_pi binder b = bind_pis [binder] b

 (** for a type p of the form (p_1:P_1) -> ... -> (p_n:P_n) -> (e:E) ** J we
     return [p_n,P_n;...;p_1,P_n],(e,E),J. *)
let unbind p : binder list * binder option * lf_type =
  let rec repeat binders p =
    match unmark p with
    | F_Pi(v,a,b) -> repeat ((get_pos p,v,a) :: binders) b
    | F_Sigma(v,a,b) -> binders, Some (get_pos p,v,a), b
    | _ -> [], None, bind_pis binders p
  in
  repeat [] p

let rec bind_sigma binder b =
  match binder with
  | Some (pos,v,a) -> with_pos pos (F_Sigma(v,a,b))
  | None -> b

 (** Suppose t has the form P -> (e:E) ** J and u has the form Q -> (f:F) ** K.
     We think of an instance of t as providing a parametrized expression of
     type P -> E together with a judgment of type J about the expression, and
     similarly for u.  We return a new type describing a parametrized
     expression of type (P->E)->(Q->F) together with a judgment about it, of
     type (P->J)->K.  The resulting type looks like e:(P -> E) -> Q -> (f:F) **
     (P -> J) -> K.  All this goes through if t has the form P_1 -> ... -> P_n
     -> (e:E) ** J, and similarly for u, because we can rewrite it in terms of
     P = P_1 ** ... ** P_n. We intend to use this as the basis for the
     statement of all theorems and axioms. *)
let pi1_relative_implication t u =
  let (p,e,j) = unbind t in
  let (q,f,k) = unbind u in
  match e with
  | Some (pos,e,ee) ->
      let fix t = Substitute.subst_type (e,apply_vars (var_to_lf_pos pos e) (List.rev p)) t in
      let j = fix j in
      bind_pi (pos,e,(bind_pis p ee)) (bind_pis q (bind_sigma f (arrow (bind_pis p j) k)))
  | None -> raise NotImplemented

let apply_binder_1 pos (c:(var marked * lf_expr) list) v t1 t2 u = 
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

let apply_binder_2 pos (c:(var marked * lf_expr) list) (v : var marked) (t1 : lf_type) (t2 : lf_expr -> lf_type) (u : lf_type) = 
  (* syntax is { v_1 : T_1 , ... , v_n : T_n |- v Type } u  or  { v_1 : T_1 , ... , v_n : T_n |- v:T } u *)
  (* t1 is texp or oexp; t2 is (fun t -> istype t) or (fun o -> hastype o t) *)
  let (vpos,v) = v in
  let c = List.map (fun ((vpos,v),t) -> vpos, F_Sigma(v,oexp,hastype (var_to_lf_pos pos v) t)) c in
  let t = pos, F_Sigma(v,t1,t2 (var_to_lf_pos pos v)) in
  let t = List.fold_right pi1_relative_implication c t in
  let u = pi1_relative_implication t u in
  unmark u

let apply_binder pos c v t1 t2 u =
  match !Toplevel.binder_mode with
  | Toplevel.Binder_mode_relative -> apply_binder_2 pos c v t1 t2 u
  | Toplevel.Binder_mode_pairs -> apply_binder_1 pos c v t1 t2 u

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
  Universes Tilde Singleton Dollar LF TS Kpair K_1 K_2 K_CAR K_CDR Times Slash
  Turnstile DoubleArrow DoubleArrowFromBar ColonColonEqual ColonEqual Theorem
  LeftBrace RightBrace TurnstileDouble ColonColon Include Clear Mode Single
  Relative Pairs

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

  Star					(* [El] *)

%left

  Slash					(* substitution *)

%right

  (* These are the tokens that can begin a TS-expression, and
     thus might be involved in the decision about reducing an application: *)

  IDENTIFIER Underscore LeftParen Kumax CONSTANT_SEMI CONSTANT Lambda
  Sigma Pi VARIABLE Dollar

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

    | f= lf_type_constant args= list(lf_expr)
	{ F_Apply(f,args) }

    | Pi v= variable Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
	{ F_Pi(v,a,b) }

    | Sigma v= variable Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
	{ F_Sigma(v,a,b) }

    | a= lf_type Times b= lf_type
	{ F_Sigma(newunused(),a,b) }

    | LeftParen v= variable Colon a= lf_type RightParen Times b= lf_type
	{ F_Sigma(v,a,b) }

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

    | LeftBracket a= lf_expr Equal b= lf_expr Colon t= lf_expr RightBracket
	{ unmark (object_equality a b t) }

    | LeftBracket t= lf_expr Equal u= lf_expr RightBracket
	{ unmark (type_equality t u) }

    | LeftBracket t= lf_expr Tilde u= lf_expr Type RightBracket
	{ unmark (type_uequality t u) }

    | LeftBracket a= lf_expr Tilde b= lf_expr Colon t= lf_expr RightBracket
	{ unmark (object_uequality a b t) }

    | a= lf_type Turnstile b= lf_type
	{ unmark (pi1_relative_implication a b) }

    | v= marked_variable Type
	{ let (pos,v) = v in F_Sigma(v,texp,istype (var_to_lf_pos pos v)) }

    | v= marked_variable ColonColon t= lf_expr
	{ let (pos,v) = v in F_Sigma(v,oexp,hastype (var_to_lf_pos pos v) t) }

    | v= marked_variable ColonColonEqual e= lf_expr ColonColon t= lf_expr
	{ let (pos,v) = v in F_Sigma(v,with_pos_of e (F_Singleton(e,oexp)),hastype (var_to_lf_pos pos v) t) }

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

    | LeftParen Kpair a= lf_expr b= lf_expr RightParen
	{ CONS(a, b) }

    | LeftParen a= lf_expr Comma b= lf_expr RightParen
	{ CONS(a, b) }

    | Lambda v= marked_variable_or_unused Comma body= lf_expr
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

    | LeftParen head_and_args= lf_expr_head_and_reversed_spine RightParen
	{ let (hd,args) = head_and_args in APPLY(hd,reverse_spine args) }

lf_expr_head_and_reversed_spine:

    | head_and_args= lf_expr_head_and_reversed_spine arg= lf_expr
	{ app head_and_args arg }

    | head_and_args= short_head_and_reversed_spine arg= lf_expr
	{ app head_and_args arg }

    | head_and_args= lf_expr_head_and_reversed_spine K_CAR
	{ car head_and_args }

    | head_and_args= short_head_and_reversed_spine K_CAR
	{ car head_and_args }

    | head_and_args= lf_expr_head_and_reversed_spine K_CDR
	{ cdr head_and_args }

    | head_and_args= short_head_and_reversed_spine K_CDR
	{ cdr head_and_args }

short_head_and_reversed_spine:

    | tsterm_head
	{ $1, END }

    | variable
	{ V $1, END }

    | head_and_args= short_head_and_reversed_spine K_1
    	{ car head_and_args }

    | head_and_args= short_head_and_reversed_spine K_2
    	{ cdr head_and_args }

    | tac= tactic_expr
	{ TAC tac, END }

    | head_and_args= parenthesized(lf_expr_head_and_reversed_spine) K_1
    	{ car head_and_args }

    | head_and_args= parenthesized(lf_expr_head_and_reversed_spine) K_2
    	{ cdr head_and_args }

tactic_expr:

    | Dollar name= IDENTIFIER
	{ Tactic_name name }

    | Dollar index= NUMBER
	{ Tactic_index index }

dotted_number: n= separated_nonempty_list(Period,NUMBER) {n}

command: c= unmarked_command { Position($startpos, $endpos), c }

unmarked_command:

    | EOF
	{ trap(); raise Eof }

    | Variable vars= nonempty_list(IDENTIFIER) Type Period
	{ Toplevel.Variable vars }

    | Variable vars= nonempty_list(IDENTIFIER) Ulevel eqns= preceded(Semicolon,uEquation)* Period
	{ Toplevel.UVariable (vars,eqns) }

    | Axiom num= option(dotted_number) name= IDENTIFIER t= ts_judgment Period
	{ Toplevel.Axiom (num,name,t) }

    | Axiom LF num= option(dotted_number) name= IDENTIFIER Colon t= lf_type Period
	{ Toplevel.Axiom (num,name,t) }

    | Check TS o= ts_expr Period
	{ Toplevel.CheckTS o }

    | Check LF e= lf_expr Period
	{ Toplevel.CheckLF e }

    | Check TS Colon t= ts_judgment Period
	{ Toplevel.CheckLFtype t }

    | Check LF Colon t= lf_type Period
	{ Toplevel.CheckLFtype t }

    | Check Universes Period
	{ Toplevel.CheckUniverses }

    | Alpha e1= ts_expr Equal e2= ts_expr Period
	{ Toplevel.Alpha (e1, e2) }

    | Theorem LF name= IDENTIFIER Colon thm= lf_type ColonEqual deriv= lf_expr Period 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Theorem name= IDENTIFIER thm= ts_judgment ColonColonEqual deriv= lf_expr Period 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Theorem name= IDENTIFIER thm= ts_judgment ColonEqual deriv= ts_expr Period 
	{ 
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Include filename= STRING Period { Toplevel.Include filename }
    | Clear Period { Toplevel.Clear }
    | Show Period { Toplevel.Show None }
    | Show n= NUMBER Period { Toplevel.Show (Some n) }
    | End Period { Toplevel.End }
    | Mode Single Period { Toplevel.Mode_single }
    | Mode Pairs Period { Toplevel.Mode_pairs }
    | Mode Relative Period { Toplevel.Mode_relative }

marked_variable:

    | IDENTIFIER
	{ Position($startpos, $endpos), Var $1 }

uEquation:

    | u= ts_expr Equal v= ts_expr 
	{ (u,v) }

    | v= ts_expr GreaterEqual u= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }

    | u= ts_expr LessEqual v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max u v), v }

    | v= ts_expr Greater u= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

    | u= ts_expr Less v= ts_expr 
	{ let pos = Position($startpos, $endpos) in (pos, make_U_max (pos, make_U_next u) v), v }

parenthesized(X): x= delimited(LeftParen,X,RightParen) {x}

list_of_parenthesized(X): list(parenthesized(X)) {$1}

ts_exprEof: a= ts_expr EOF {a}

ts_judgment:

    | LeftParen t= unmarked_ts_judgment RightParen
	{ Position($startpos, $endpos), t }

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
	{ unmark (pi1_relative_implication a b) }

(* base judgments *)

    | Type
	{ let pos = Position($startpos, $endpos) in
	  let v = Var "t" in
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
	  F_Sigma(v, with_pos pos (F_Singleton(a,texp)), with_pos pos (F_Apply(F_istype, [var_to_lf_pos pos v]))) }

    | LeftBracket a= ts_expr Type RightBracket
	{ unmark (istype a) }

    | LeftBracket a= ts_expr Equal b= ts_expr RightBracket
	{ unmark (type_equality a b) }

    | LeftBracket x= ts_expr Colon t= ts_expr RightBracket
	{ unmark (hastype x t) }

    | LeftBracket x= ts_expr Equal y= ts_expr Colon t= ts_expr RightBracket
	{ unmark (object_equality x y t) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Ulevel RightBracket
	{ unmark (ulevel_equality a b) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Type RightBracket
	{ unmark (type_uequality a b) }

    | LeftBracket a= ts_expr Tilde b= ts_expr Colon t= ts_expr RightBracket
	{ unmark (object_uequality a b t) } 

(* introduction of parameters *)

    | LeftBrace c= context vbj= separated_nonempty_list(Comma,pair(nonempty_list(marked_variable),binder_judgment)) RightBrace u= ts_judgment
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

    | c= terminated( separated_list( Comma,
			  separated_pair(
			       marked_variable_or_unused,
			       Colon, ts_expr)),
		     Turnstile)
	{c}

tsterm_head:

    | name= CONSTANT
	{ try List.assoc name Names.lf_expr_head_strings with Not_found -> V (Var name) }

arglist:

    | LeftParen a= separated_list(Comma,ts_expr) RightParen
	{a}

(* it's tempting to include '_' (Underscore) as a variable but there would be an 
    ambiguity when looking at the start [ _ |-> x ] and [ _ ].  In the first case,
   it's an unused variable, and in the second case, it's an empty hole. *)

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

unmarked_ts_expr:

    | v= marked_variable_or_unused DoubleArrowFromBar body= ts_expr
	{ let (pos,v) = v in
	  let (v,body) = Substitute.subst_fresh pos (v,body) in 
	  LAMBDA(v,body) }

    | e= ts_expr K_1
    	{ unmark ( Substitute.apply_args e (CAR END) ) }

    | e= ts_expr K_2
    	{ unmark ( Substitute.apply_args e (CDR END) ) }

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

    | name= CONSTANT_SEMI vars= separated_list(Comma,marked_variable_or_unused) RightBracket args= arglist
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

