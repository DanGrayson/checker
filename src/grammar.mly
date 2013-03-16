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

%token <string> CONSTANT CONSTANT_SEMI STRING NAME NAME_W

%token
  LeftParen RightParen RightBracket LeftBracket Comma Period Colon Star Arrow
  ArrowFromBar Equal Underscore Axiom GreaterEqual Greater LessEqual Less
  Semicolon Ulevel Kumax Type Pi Lambda Sigma Check Show End Variable Alpha EOF
  Universes Tilde Singleton Dollar LF TS Kpair K_1 K_2 K_CAR K_CDR Times
  Turnstile DoubleArrow DoubleArrowFromBar ColonColonEqual ColonEqual Theorem
  LeftBrace RightBrace TurnstileDouble ColonColon Include Clear EqualEqual
  TTS Back BackTo Mode

(* precedences, lowest first *)

%right

  Reduce_binder

%right

  Turnstile
  TurnstileDouble

%right

  DoubleArrowFromBar			(* TS notation for LF lambda *)
  ArrowFromBar				(* TS notation for TS lambda *)
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

  Underscore LeftParen Kumax CONSTANT_SEMI CONSTANT Lambda Sigma Pi Dollar NAME
  NAME_W

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

    | Pi v= identifier Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
	{ make_F_Pi a (v,b) }

    | Sigma v= identifier Colon a= lf_type Comma b= lf_type
	%prec Reduce_binder
    | LeftParen v= identifier Colon a= lf_type RightParen Times b= lf_type
	{ make_F_Sigma a (v,b) }

    | a= lf_type Times b= lf_type
	{ make_F_Sigma_simple a b }

    | LeftParen v= identifier Colon a= lf_type RightParen Arrow b= lf_type
       { make_F_Pi a (v,b) }

    | a= lf_type Arrow b= lf_type
       { unmark (a @-> b) }

    | Singleton LeftParen x= lf_expr Colon t= lf_type RightParen
	{ F_Singleton(x,t) }

    | LeftBracket t= lf_expr Type RightBracket
	{ unmark (if !ts_mode then istype t else istype_embedded_witnesses t) }

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
    	{ let v = good_var_name a (id "foo") in (* the "|-" operator is not fully implemented yet *)
	  let v = get_pos a, v in
	  unmark (pi1_implication (v,a) b) }

    | v= marked_identifier Type
	{ let (pos,v) = v in make_F_Sigma texp (v,(if !ts_mode then istype_v else istype_embedded_witnesses_v) pos v) }

    | v= marked_identifier ColonColon t= lf_expr
	{ let (pos,v) = v in make_F_Sigma oexp (v,hastype (id_to_expr pos v) t) }

    | v= marked_identifier ColonColonEqual e= lf_expr ColonColon t= lf_expr
	{ let (pos,v) = v in make_F_Sigma (with_pos_of e (F_Singleton(e,oexp))) (v,hastype (id_to_expr pos v) t) }

lf_type_constant:

    | l= NAME
	{ let pos = Position($startpos, $endpos) in lookup_type_constant pos l }

lf_expr:

    | e= unmarked_lf_expr
	{(Position($startpos, $endpos), e)}

    | e= parenthesized(lf_expr) {e}

unmarked_lf_expr:

    | LeftParen Kpair a= lf_expr b= lf_expr RightParen
    | LeftParen a= lf_expr Comma b= lf_expr RightParen
	{ CONS(a, b) }

    | Lambda v= marked_identifier_or_unused Comma body= lf_expr
    | v= marked_identifier_or_unused ArrowFromBar body= lf_expr
	{ unmark (lambda1 (unmark v) body) }

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

    | identifier
	{ V (Var $1), END }

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

    | Dollar name= NAME
	{ Tactic_name name }

    | Dollar index= NUMBER
	{ Tactic_index index }

tactic_expr:

    | s= tactic_expr_2
	{s}

    | s= tactic_expr_2 Semicolon t= tactic_expr
	{ Tactic_sequence (s,t) }

tactic_expr_2:

    | name= NAME
	{ Tactic_name name }

dotted_number: n= separated_nonempty_list(Period,NUMBER) {n}

command:

    | c= unmarked_command
	{ Position($startpos, $endpos), c }

    | error				(* instant error return for the sake of Proof General *)
    (* | error Period *)
    (* | error EOF *)
	{ let pos = Position($startpos, $endpos) in
	  fprintf stderr "%a: syntax error\n%!" _pos pos;
	  bump_error_count pos;
	  pos, Toplevel.SyntaxError }

    | EOF { raise Eof }

unmarked_command:

    | Variable vars= marked_name+ Colon t= ts_expr Period
	{ Toplevel.OVariable (vars,t) }

    | Variable vars= marked_name+ Type Period
	{ Toplevel.TVariable vars }

    | Variable vars= marked_name+ Ulevel eqns= preceded(Semicolon,uEquation)* Period
	{ Toplevel.UVariable (vars,eqns) }

    | Axiom num= dotted_number? name= NAME t= ts_judgment Period
	{ Toplevel.Axiom (num,id name,t) }

    | Axiom LF num= dotted_number? name= identifier Colon t= lf_type Period
	{ Toplevel.Axiom (num,name,t) }

    | Check TS? o= ts_expr Period
	{ Toplevel.CheckTS o }

    | Check LF e= lf_expr Period
	{ Toplevel.CheckLF e }

    | Check TS? Colon t= ts_judgment Period
    | Check LF Colon t= lf_type Period
	{ Toplevel.CheckLFtype t }

    | Check TTS Colon t= ts_judgment Period
	{ Toplevel.CheckWitness t }

    | Check Universes Period
	{ Toplevel.CheckUniverses }

    | Alpha e1= ts_expr EqualEqual e2= ts_expr Period
	{ Toplevel.Alpha (e1, e2) }

    | Theorem LF name= NAME Colon thm= lf_type ColonEqual deriv= lf_expr Period
    | Theorem name= NAME thm= ts_judgment ColonColonEqual deriv= lf_expr Period
    | Theorem name= NAME thm= ts_judgment ColonEqual deriv= ts_expr Period
	{
	  let pos = Position($startpos, $endpos) in
	  Toplevel.Theorem (pos, name, deriv, thm) }

    | Include filename= STRING Period
	{ Toplevel.Include filename }

    | Clear Period
	{ Toplevel.Clear }

    | Show n= NUMBER? Period
	{ Toplevel.Show n }

    | Back n= NUMBER? Period
	{ let n = match n with Some n -> n | None -> 1 in Toplevel.Back n }

    | BackTo n= NUMBER Period
	{ Toplevel.BackTo n }

    | Mode TTS Period
	{ Toplevel.Mode "TTS" }

    | Mode TS Period
	{ Toplevel.Mode "TS" }

    | End Period
	{ Toplevel.End }

marked_identifier:

    | identifier
	{ Position($startpos, $endpos), $1 }

marked_name:

    | NAME
	{ Position($startpos, $endpos), $1 }

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

    | LeftParen v= identifier Colon a= ts_judgment RightParen DoubleArrow b= ts_judgment
	{ make_F_Pi a (v,b) }

    | a= ts_judgment DoubleArrow b= ts_judgment
	{ unmark (a @-> b) }

    | LeftParen v= identifier Colon a= ts_judgment RightParen Times b= ts_judgment
	{ make_F_Sigma a (v,b) }

    | a= ts_judgment Times b= ts_judgment
	{ make_F_Sigma_simple a b }

    | a= ts_judgment TurnstileDouble b= ts_judgment
    	{ let v = good_var_name a (id "foo") in (* the "|-" operator is not fully implemented yet *)
	  let v = get_pos a, v in
	  unmark (pi1_implication (v,a) b) }

(* base judgments *)

    | Type
	{ let pos = Position($startpos, $endpos) in
	  let v = id "T" in
	  make_F_Sigma texp (v,(if !ts_mode then istype_v else istype_embedded_witnesses_v) pos v) }

    | Colon t= ts_expr
	{ let v = id "o" in
	  let pos = get_pos t in
	  make_F_Sigma oexp (v,with_pos pos (F_Apply(F_hastype, [id_to_expr pos v; t]))) }

    | Turnstile x= ts_expr Colon t= ts_expr
	{ unmark (this_object_of_type (get_pos x) x t) }

    | Turnstile a= ts_expr Type
        { let v = id "t" in
          let pos = get_pos a in
          let a = with_pos pos (F_Singleton(a,texp)) in
          let b = if !ts_mode then istype_v pos v else istype_embedded_witnesses_v pos v in
          make_F_Sigma a (v,b)
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
	  unmark w }

    | LeftBrace c= context vbj= separated_nonempty_list(Comma,pair(marked_identifier+,binder_judgment)) RightBrace u= ts_judgment
	%prec Reduce_binder
	{
	  let pos = Position($startpos, $endpos) in
	  let r = List.fold_right
	      (
	       fun (v,bj) u ->
		 let f = match bj with
		 | ULEV ->
		     if c <> [] then $syntaxerror;
		     fun v u -> with_pos_of v (make_F_Pi uexp (unmark v, u))
		 | IST ->
		     fun v u -> apply_binder pos c v texp u (if !ts_mode then istype_v else istype_embedded_witnesses_v)
		 | HAST t ->
		     fun v u -> apply_binder pos c v oexp u (hastype_v t)
		 | W_HAST(o,t) ->
		     fun v u -> 
		       let o' = id_to_expr (get_pos o) (unmark o) in
		       let u = apply_binder pos c v wexp u (witnessed_hastype_v t o') in
		       let w = bind_pi (pos,unmark o,oexp) u in
		       printf " binder result = %a\n%!" _t (empty_environment,w);
		       w
		 | W_TEQ(t1,t2) ->
		     fun v u -> apply_binder pos c v wexp u (witnessed_type_equality_v t1 t2)
		 | W_OEQ(o1,o2,t) ->
		     fun v u -> apply_binder pos c v wexp u (witnessed_object_equality_v t o1 o2)
		 in List.fold_right f v u)
	      vbj u in
	  unmark r
	}

ts_bracketed_judgment:

    | LeftBracket a= ts_expr Type RightBracket
	{ unmark (if !ts_mode then istype a else istype_embedded_witnesses a) }

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

    | LeftBracket p= ts_expr Colon x= ts_expr Colon t= ts_expr RightBracket
	{ unmark (witnessed_hastype t x p) }

    | LeftBracket p= ts_expr Colon a= ts_expr EqualEqual b= ts_expr RightBracket
	{ unmark (witnessed_type_equality a b p) }

    | LeftBracket p= ts_expr Colon x= ts_expr EqualEqual y= ts_expr Colon t= ts_expr RightBracket
	{ unmark (witnessed_object_equality t x y p) }

binder_judgment:

    | Ulevel { ULEV }

    | Type { IST }

    | Colon t= ts_expr { HAST t }

    | Colon o= marked_identifier Colon t= ts_expr { W_HAST(o,t) }

    | Colon x= ts_expr EqualEqual y= ts_expr { W_TEQ(x,y) }

    | Colon x= ts_expr EqualEqual y= ts_expr Colon t= ts_expr { W_OEQ(x,y,t) }

context:

    | c= terminated( separated_list( Comma,
			  separated_pair(
			       marked_identifier_or_unused,
			       Colon, ts_expr)),
		     Turnstile)
	{c}

tsterm_head:

    | name= CONSTANT
	{ let pos = Position($startpos, $endpos) in try lookup_label pos name with Not_found -> $syntaxerror }

arglist:

    | LeftBracket a= separated_list(Comma,ts_expr) RightBracket
	{a}

empty_hole: Underscore { default_tactic }

unused_identifier: Underscore { id "_" }

identifier:

    | NAME { id $1 }
    | NAME_W { idw $1 }

identifier_or_unused: identifier {$1} | unused_identifier {$1}

marked_identifier_or_unused: identifier_or_unused { Position($startpos, $endpos), $1 }

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

    | v= marked_identifier_or_unused DoubleArrowFromBar body= ts_expr
	{ unmark (lambda1 (unmark v) body) }

    | e= ts_expr K_1
    	{ unmark ( Substitute.apply_args e (CAR END) ) }

    | e= ts_expr K_2
    	{ unmark ( Substitute.apply_args e (CDR END) ) }

    | tac= closed_tactic_expr
	{ cite_tactic tac END }

    | f= ts_expr LeftBracket o= separated_list(Comma,ts_spine_member) RightBracket
	{ unmark (Substitute.apply_args f (spine_member_list_to_spine o)) }

    | identifier
	{ APPLY(V (Var $1),END) }

    | empty_hole {$1}

    | f= ts_expr o= ts_expr
	%prec Reduce_application
	{ let pos = Position($startpos, $endpos) in
	  if !ts_mode
	  then APPLY(O O_ev,  f ** o ** (pos, default_tactic) ** END) 
	  else APPLY(O O_ev', f ** o ** (pos, default_tactic) ** (pos, default_tactic) ** END) 
	}

    | LeftParen x= identifier Colon t= ts_expr RightParen ArrowFromBar o= ts_expr
    | Lambda x= identifier Colon t= ts_expr Comma o= ts_expr
	%prec Reduce_binder
	{ 
	  if !ts_mode
	  then make_O_lambda  t (x,o) 
	  else make_O_lambda' t (x,o) 
	}

    | Star o= ts_expr
	{ let pos = Position($startpos, $endpos) in
	  if !ts_mode then make_T_El o else make_T_El' o (pos, (cite_tactic (Tactic_name "default") END)) }

    | Pi x= identifier Colon t1= ts_expr Comma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Pi t1 (x,t2) }

    | LeftParen x= identifier Colon t= ts_expr RightParen Arrow u= ts_expr
	{ if !ts_mode then make_T_Pi t (x,u) else make_T_Pi' t (lambda1 x (lambda1 (witness_id x) u)) }

    | x= ts_expr Equal y= ts_expr
	{ make_T_Id (with_pos_of x (cite_tactic (Tactic_name "tn12") END)) x y }

    | t= ts_expr Arrow u= ts_expr
	{ if !ts_mode then make_T_Pi t (id "_",u) else make_T_Pi' t (lambda1 (id "_") (lambda1 (idw "_") u)) }

    | Sigma x= identifier Colon t1= ts_expr Comma t2= ts_expr
	%prec Reduce_binder
	{ make_T_Sigma t1 (x,t2) }

    | Kumax LeftParen u= ts_expr Comma v= ts_expr RightParen
	{ APPLY(U U_max, u**v**END)  }

    | label= tsterm_head
	{ APPLY(label, END ) }

    | LeftParen a= ts_expr Comma b= ts_expr RightParen
	{ CONS(a,b) }

    | name= CONSTANT_SEMI vars= separated_list(Comma,marked_identifier_or_unused) RightBracket args= arglist
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
		 (* examples:
		    1: if indices = [ SingleVariable 0; SingleVariable 1], change arg to (LAMBDA v0 , (LAMBDA v1, arg))
		    2: if indices = [ WitnessPair 0                     ], change arg to (LAMBDA v0$, (LAMBDA v0, arg))
		  *)
		 List.fold_right (
		 fun wrapped_index arg -> with_pos (get_pos arg) (
		   match wrapped_index with
		   | SingleVariable index -> unmark (lambda1 (unmark (List.nth vars index)) arg)
                   | WitnessPair index ->
                       let (pos,v) = List.nth vars index in
                       let p = witness_id v in
		       unmark (lambda2 v p arg)
		  )
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

