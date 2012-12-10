(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    [EEST]: Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676-722.
*)

(*

  We probably don't handle types such as [Pi x:A, Singleton(B)] well.

*)

open Error
open Variables
open Typesystem
open Names
open Printer
open Substitute
open Printf
open Helpers
open Tau

let abstraction1 (env:context) = function
  | [CAN t; LAMBDA(x, _)] -> ts_bind (x,t) env
  | _ -> env

let abstraction2 (env:context) = function
  | [_; _; CAN n; LAMBDA(x,_)] -> ts_bind (x,(get_pos n, make_TT_El n)) env
  | _ -> env

let abstraction3 (env:context) = function
  | [CAN f; _; LAMBDA(x, _)] -> 
      let tf = tau env f in (
      match unmark tf with
      | APPLY(T T_Pi, [_; LAMBDA(x, CAN t)]) -> ts_bind (x,t) env
      | _ -> env)
  | _ -> env

let ts_binders = [
  ((O O_lambda, 1), abstraction1);
  ((T T_Pi, 1), abstraction1);
  ((T T_Sigma, 1), abstraction1);
  ((O O_forall, 3), abstraction2);
  ((O O_ev, 2), abstraction3)
]

let apply_ts_binder env i = function
  | APPLY(h,args) -> (
      try (List.assoc (h,i) ts_binders) env args
      with Not_found -> env)
  | _ -> raise Internal

let try_alpha = false (* turning this on could slow things down a lot before we implement hash codes *)

let err env pos msg = raise (TypeCheckingFailure (env, pos, msg))

let errmissingarg env pos a = err env pos ("missing next argument, of type "^lf_type_to_string a)

let mismatch_type env pos t pos' t' = 
  raise (TypeCheckingFailure2 (env,
	 pos , "expected type "^lf_type_to_string t ,
	 pos', "to match      "^lf_type_to_string t'))

let mismatch_term_t env pos x pos' x' t = 
  raise (TypeCheckingFailure3 (env,
		    pos , "expected term\n\t"^lf_expr_to_string x ,
		    pos',      "to match\n\t"^lf_expr_to_string x',
	       get_pos t,	"of type\n\t"^lf_type_to_string t))

let mismatch_term env pos x pos' x' = 
  raise (TypeCheckingFailure2 (env,
		    pos , "expected term\n\t"^lf_expr_to_string x ,
		    pos',      "to match\n\t"^lf_expr_to_string x'))

let rec strip_singleton ((_,(_,t)) as u) = match t with
| F_Singleton a -> strip_singleton a
| _ -> u

(* background assumption: all types in the environment have been verified *)

type surrounding = (int * atomic_expr) option

type tactic_function =
       surrounding         (* the ambient APPLY(...), if any, and the index among its head and arguments of the hole *)        
    -> context							      (* the active context *)
    -> position							      (* the source code position of the tactic hole *)
    -> lf_type							      (* the type of the hole, e.g., [texp] *)
 -> lf_expr option									 (* the proffered expression *)

let tactics : (string * tactic_function) list ref = ref []

let apply_tactic surr env pos t = function
  | Q_name name ->
      let tactic = 
	try List.assoc name !tactics
	with Not_found -> err env pos ("unknown tactic: "^name)
      in
      tactic surr env pos t
  | Q_index n ->
      let (v,u) = 
	try List.nth env n 
	with Failure nth -> err env pos ("index out of range: "^string_of_int n)
      in
      if Alpha.UEqual.type_equiv empty_uContext t u then Some(var_to_lf v)
      else mismatch_type env pos t (get_pos u) u

let unfold env v =
  match unmark( lookup_type env v ) with
  | F_Singleton a -> let (x,t) = strip_singleton a in x
  | _ -> raise Not_found		(* What if the type is effectively a singleton, such as Sing(x)*Sing(y) ? *)

let rec natural_type (pos:position) (env:context) (x:lf_expr) : lf_type =
  (* assume nothing *)
  (* see figure 9 page 696 [EEST] *)
  match x with
  | CAN (pos,x) -> (
      match x with
      | TacticHole _ -> raise NotImplemented
      | EmptyHole _ -> err env pos "empty hole found"
      | APPLY(l,args) -> 
	  let t = label_to_type env pos l in
	  let rec repeat i args t =
	    match args, unmark t with
	    | x :: args, F_Pi(v,a,b) -> 
		repeat (i+1) args (subst_type (v,x) b)
	    | x :: args, _ -> err env pos "at least one argument too many"
	    | [], F_Pi(v,a,b) -> errmissingarg env pos a (* we insist on eta-long format *)
	    | [], t -> t
	  in nowhere 5 (repeat 0 args t)
      | PR1 xy -> (
	  match unmark (natural_type pos env xy) with
	  | F_Sigma(v,a,b) -> a
	  | _ -> raise Internal)
      | PR2 xy -> (
	  let (xypos,xy0) = natural_type pos env xy in
	  match xy0 with
	  | F_Sigma(v,a,b) -> subst_type (v,CAN(xypos, PR1 xy)) b
	  | _ -> raise Internal)
     )
  | LAMBDA _ -> err env pos "LF lambda expression found, has no natural type"
  | PAIR _ -> err env pos "LF pair found, has no natural type"

let rec head_reduction (env:context) (x:lf_expr) : lf_expr =
  (* assume nothing *)
  (* see figure 9 page 696 [EEST] *)
  (* may raise Not_found if there is no head reduction *)
  match x with
  | CAN (pos,x) -> (
      match x with
      | PR1(PAIR(_,x,_)) -> x
      | PR2(PAIR(_,_,y)) -> y
      | PR1 e -> CAN(pos,PR1(head_reduction env e))
      | PR2 e -> CAN(pos,PR2(head_reduction env e))
      | APPLY(V v, args) -> let f = unfold env v in apply_args pos f args
      | APPLY _ -> raise Not_found
      | TacticHole _ -> raise NotImplemented
      | EmptyHole _ -> err env pos "empty hole found"
     )
  | PAIR _ | LAMBDA _ -> raise Not_found

let rec head_normalization (env:context) (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  try head_normalization env (head_reduction env x)
  with Not_found -> x

let rec num_args t = match unmark t with 
  | F_Pi(_,_,b) -> 1 + num_args b
  | _ -> 0

let rec term_normalization (env:context) (x:lf_expr) (t:lf_type) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  let (pos,t0) = t in
  match t0 with 
  | F_Pi(v,a,b) -> (
      match x with
      | LAMBDA(w,body) ->
	  let b    = subst_type (v,var_to_lf w) b in
	  let body = term_normalization ((w,a) :: env) body b in
	  LAMBDA(w,body)
      | _ -> raise Internal)
  | F_Sigma(v,a,b) ->
      let pos = get_pos_lf x in
      let x,y = CAN(pos,PR1 x),CAN(pos,PR2 x) in
      PAIR(pos,
	   term_normalization env x a,
	   term_normalization env y (subst_type (v,x) b))
  | F_APPLY _
  | F_Singleton _ ->
      let x = head_normalization env x in
      let (x,t) = path_normalization env pos x in
      x
      
and path_normalization (env:context) pos (x:lf_expr) : lf_expr * lf_type =
  (* returns the normalized term x and the inferred type of x *)
  (* see figure 9 page 696 [EEST] *)
  (* assume x is head normalized *)
  match x with
  | LAMBDA _ -> err env pos "path_normalization encountered a function"
  | PAIR _ -> err env pos "path_normalization encountered a pair"
  | CAN y ->
      let (pos,y0) = y in
      match y0 with
      | TacticHole _ -> raise NotImplemented
      | EmptyHole _ -> err env pos "path_normalization encountered an empty hole"
      | PR1 p -> (
	  let p',s = path_normalization env pos p in
	  match unmark s with 
	  | F_Sigma(v,a,b) -> CAN(pos,PR1 p'), a
	  | _ -> raise Internal)
      | PR2 p -> (
	  let p',s = path_normalization env pos p in
	  match unmark s with 
	  | F_Sigma(v,a,b) -> CAN(pos,PR2 p'), subst_type (v,CAN(pos,PR1 p')) b
	  | _ -> raise Internal)
      | APPLY(f,args) ->
	  let t0 = label_to_type env pos f in
	  let (t,args) =
	    let rec repeat t args : lf_type * lf_expr list = (
	      match unmark t with
	      | F_Pi(v,a,b) -> (
		  match args with
		  | [] -> raise (TypeCheckingFailure2 (env,
		    pos , ("expected "^string_of_int (num_args t)^" more arguments"),
		    (get_pos t0), (" using:\n\t"^lf_expr_head_to_string f^" : "^lf_type_to_string t0)))
		  | x :: args ->
		      let b = subst_type (v,x) b in
		      let x = term_normalization env x a in
		      let (c,args) = repeat b args in
		      (c, x :: args))
	      | F_Singleton _ -> raise Internal (* x was head normalized, so any definition of f should have been unfolded *)
	      | _ -> (
		  match args with
		  | [] -> (t,[])
		  | x :: args -> err env pos "unexpected argument"))
	    in repeat t0 args
	  in (CAN(pos,APPLY(f,args)), t)

let rec type_normalization (env:context) (t:lf_type) : lf_type =
  (* see figure 9 page 696 [EEST] *)
  let (pos,t0) = t in
  let t = match t0 with
  | F_Pi(v,a,b) -> 
      let a' = type_normalization env a in
      let b' = type_normalization ((v,a) :: env) b in
      F_Pi(v,a',b')
  | F_Sigma(v,a,b) -> 
      let a' = type_normalization env a in
      let b' = type_normalization ((v,a) :: env) b in
      F_Sigma(v,a',b')
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let args =
	let rec repeat env kind (args:lf_expr list) = 
	  match kind, args with 
	  | K_type, [] -> []
	  | K_type, x :: args -> err env pos "too many arguments"
	  | K_Pi(v,a,kind'), x :: args ->
	      term_normalization env x a ::
	      repeat ((v,a) :: env) kind' args
	  | K_Pi(_,a,_), [] -> errmissingarg env pos a
	in repeat env kind args
      in F_APPLY(head,args)
  | F_Singleton(x,t) -> 
      F_Singleton( term_normalization env x t, type_normalization env t )
  in (pos,t)


let rec type_validity (env:context) (t:lf_type) : lf_type =
  (* assume the kinds of constants, and the types in them, have been checked *)
  (* driven by syntax *)
  (* return the same type t, but with tactic holes replaced *)
  (* see figure 12, page 715 [EEST] *)
  let (pos,t) = t 
  in 
  ( pos,
    match t with 
    | F_Pi(v,t,u) ->
	let t = type_validity env t in
	let u = type_validity ((v,t) :: env) u in
	F_Pi(v,t,u)
    | F_Sigma(v,t,u) ->
	let t = type_validity env t in
	let u = type_validity ((v,t) :: env) u in
	F_Sigma(v,t,u)
    | F_APPLY(head,args) ->
	let kind = tfhead_to_kind head in
	let rec repeat env kind (args:lf_expr list) = 
	  match kind, args with 
	  | K_type, [] -> []
	  | K_type, x :: args -> err env pos "at least one argument too many";
	  | K_Pi(v,a,kind'), x :: args -> 
	      type_check None pos env x a :: repeat ((v,a) :: env) kind' args
	  | K_Pi(_,a,_), [] -> errmissingarg env pos a
	in 
	let args' = repeat env kind args in
	F_APPLY(head,args')
    | F_Singleton(x,t) -> 
	let t = type_validity env t in
	let x = type_check None pos env x t in		(* rule 46 *)
	F_Singleton(x,t))

and type_synthesis (env:context) (x:lf_expr) : lf_expr * lf_type =
  (* assume nothing *)
  (* see figure 13, page 716 [EEST] *)
  (* return a pair consisting of the original expression with any tactic holes filled in, 
     and the synthesized type *)
  match x with
  | LAMBDA _ -> err env (get_pos_lf x) ("function has no type: "^lf_expr_to_string x)
  | PAIR(pos,x,y) ->
      let x',t = type_synthesis env x in
      let y',u = type_synthesis env y in PAIR(pos,x',y'), (pos,F_Sigma(newunused(),t,u))
  | CAN e ->
      let (pos,e0) = e in
      match e0 with
      | TacticHole _ -> err env pos ("tactic hole: "^ts_expr_to_string e)
      | EmptyHole _ -> err env pos ("empty hole: "^ts_expr_to_string e)
      | PR1 p -> (
	  let p',s = type_synthesis env p in
	  match unmark s with 
	  | F_Sigma(v,a,b) -> CAN(pos,PR1 p'), a
	  | _ -> raise Internal)
      | PR2 p -> (
	  let p',s = type_synthesis env p in
	  match unmark s with 
	  | F_Sigma(v,a,b) -> CAN(pos,PR2 p'), subst_type (v,CAN(pos,PR1 p')) b
	  | _ -> raise Internal)
      (* | APPLY(V v, []) -> x, (pos, F_Singleton(CAN e, fetch_type env pos v)) *)
      | APPLY(label,args) -> (
	  let a = label_to_type env pos label in
	  let rec repeat i env (a:lf_type) (args:lf_expr list) : lf_expr list * lf_type = (
	    let (apos,a0) = a in
	    match a0, args with
	    | F_Pi(x,a',a''), m' :: args' ->
		let surr = Some(i,e) in 
		let env = apply_ts_binder env i e0 in
		let m' = type_check surr pos env m' a' in
		let (args'',u) = repeat (i+1) env (subst_type (x,m') a'') args' in
		m' :: args'', u
	    | F_Singleton(e,t), args -> repeat i env t args
	    | F_Pi _ as t, [] -> [], (pos,t) (* allow not all arguments to be present; not eta-long *)
	    | F_Sigma _ as t, [] -> [], (pos,t)
	    | F_APPLY _ as t, [] -> [], (pos,t)
	    | F_Sigma _,  arg :: _
	    | F_APPLY _, arg :: _ -> err env (get_pos_lf arg) "extra argument"
	   )
	  in
	  let (args',t) = repeat 0 env a args
	  in CAN(pos,APPLY(label,args')), t
	 )

and term_equivalence (xpos:position) (ypos:position) (env:context) (x:lf_expr) (y:lf_expr) (t:lf_type) : unit =
  (* assume x and y have already been verified to be of type t *)
  (* see figure 11, page 711 [EEST] *)
  if try_alpha && Alpha.UEqual.term_equiv empty_uContext x y then () else
  let (pos,t0) = t in
  match x, y, t0 with
  | _, _, F_Singleton _ -> ()
  | x, y, F_Sigma (v,a,b) ->
      term_equivalence xpos ypos env (CAN(xpos,PR1 x)) (CAN(ypos,PR1 y)) a;
      term_equivalence xpos ypos env (CAN(xpos,PR2 x)) (CAN(ypos,PR2 y)) (subst_type (v,CAN(xpos,PR1 x)) b)
  | x, y, F_Pi (v,a,b) -> (
      match x,y with
      | LAMBDA(t,x), LAMBDA(u,y) ->
	  let w = newfresh (Var "v") in
	  term_equivalence xpos ypos 
	    ((w,a) :: env)
	    (subst (t,var_to_lf w) x)	(* with deBruijn indices, this will go away *)
	    (subst (u,var_to_lf w) y) 
	    (subst_type (v,var_to_lf w) b)
      | x,y -> raise Internal)
  | x, y, F_APPLY(j,args) ->
      let x = head_normalization env x in
      let y = head_normalization env y in
      let t' = path_equivalence env x y in
      type_equivalence env t t'

and path_equivalence (env:context) (x:lf_expr) (y:lf_expr) : lf_type =
  (* assume x and y are head reduced *)
  (* see figure 11, page 711 [EEST] *)
  match x,y with
  | CAN (xpos,x0), CAN (ypos,y0) -> (
      match x0,y0 with
      | APPLY(f,args), APPLY(f',args') ->
	  if not (f = f') 
	  then mismatch_term env xpos x ypos y;
	  let t = label_to_type env xpos f in
	  let rec repeat t args args' =
	    match t,args,args' with
	    | t, [], [] -> t
	    | (pos,F_Pi(v,a,b)), x :: args, y :: args' ->
		term_equivalence xpos ypos env x y a;
		repeat (subst_type (v,x) b) args args'
	    | _ -> mismatch_term env xpos x ypos y
	  in repeat t args args'
      | _ -> mismatch_term env xpos x ypos y)
  | _  -> mismatch_term env (get_pos_lf x) x (get_pos_lf y) y

and type_equivalence (env:context) (t:lf_type) (u:lf_type) : unit =
  (* see figure 11, page 711 [EEST] *)
  (* assume t and u have already been verified to be types *)
  if try_alpha && Alpha.UEqual.type_equiv empty_uContext t u then () else
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  match t0, u0 with
  | F_Singleton a, F_Singleton b ->
      let (x,t) = strip_singleton a in
      let (y,u) = strip_singleton b in
      type_equivalence env t u;
      term_equivalence tpos upos env x y t
  | F_Sigma(v,a,b), F_Sigma(w,c,d)
  | F_Pi(v,a,b), F_Pi(w,c,d) ->
      type_equivalence env a c;
      let x = newfresh v in
      type_equivalence ((x, a) :: env) (subst_type (v, var_to_lf x) b) (subst_type (w, var_to_lf x) d)
  | F_APPLY(h,args), F_APPLY(h',args') ->
      (* Here we augment the algorithm in the paper to handle the type families of LF. *)
      if not (h = h') then mismatch_type env tpos t upos u;
      let k = tfhead_to_kind h in
      let rec repeat (k:lf_kind) args args' : unit =
	match k,args,args' with
	| K_Pi(v,t,k), x :: args, x' :: args' ->
	    term_equivalence tpos upos env x x' t;
	    repeat (subst_kind (v,x) k) args args'
	| K_type, [], [] -> ()
	| _ -> raise Internal
      in repeat k args args'
  | _ -> mismatch_type env tpos t upos u

and subtype (env:context) (t:lf_type) (u:lf_type) : unit =
  (* assume t and u have already been verified to be types *)
  (* driven by syntax *)
  (* see figure 12, page 715 [EEST] *)
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  match t0, u0 with
  | F_Singleton a, F_Singleton b ->
      let (x,t) = strip_singleton a in
      let (y,u) = strip_singleton b in
      type_equivalence env t u;
      term_equivalence tpos upos env x y t
  | _, F_Singleton _ -> err env tpos "expected a singleton type"
  | F_Singleton a, _ -> 
      let (x,t) = strip_singleton a in
      type_equivalence env t u
  | F_Pi(x,a,b) , F_Pi(y,c,d) ->
      subtype env c a;			(* contravariant *)
      let w = newfresh (Var "w") in
      subtype ((w, c) :: env) (subst_type (x,var_to_lf w) b) (subst_type (y,var_to_lf w) d)
  | F_Sigma(x,a,b) , F_Sigma(y,c,d) ->
      subtype env a c;			(* covariant *)
      let w = newfresh (Var "w") in
      subtype ((w, a) :: env) (subst_type (x,var_to_lf w) b) (subst_type (y,var_to_lf w) d)
  | _ -> type_equivalence env (tpos,t0) (upos,u0)

and type_check (surr:surrounding) (pos:position) (env:context) (e:lf_expr) (t:lf_type) : lf_expr = 
  (* assume t has been verified to be a type *)
  (* see figure 13, page 716 [EEST] *)
  (* we modify the algorithm to return a possibly modified expression e, with holes filled in by tactics *)
  (* We hard code one tactic:
       Fill in holes of the form [ ([ev] f o _) ] by using [tau] to compute the type that ought to go there. *)
  let (pos,t0) = t in 
  match e, t0 with
  | CAN(pos, EmptyHole _), _ ->
      raise (TypeCheckingFailure2 (env,
				   pos, "hole found : "^lf_expr_to_string e,
				   pos, "   of type : "^lf_type_to_string t))
  | CAN(pos, TacticHole tac), _ -> (
      match apply_tactic surr env pos t tac with
      | Some e -> type_check surr pos env e t
      | None ->
	  raise (TypeCheckingFailure2 (env,
				       pos, "tactic failed     : "^tactic_to_string tac,
				       pos, "  in hole of type : "^lf_type_to_string t)))

  | LAMBDA(v,e), F_Pi(w,a,b) -> (* the published algorithm is not applicable here, since
				   our lambda doesn't contain type information for the variable,
				   and theirs does *)
      let e = type_check None pos ((v,a) :: env) e (subst_type (w,var_to_lf v) b) in
      LAMBDA(v,e)

  | LAMBDA _, _ -> err env pos "did not expect a lambda expression here"

  | p, F_Sigma(w,a,b) -> (* The published algorithm omits this, correctly, but we want to 
			    give advice to tactics for filling holes in [p], so we try type-directed
			    type checking as long as possible. *)
      let (x,y) = (
	match p with			(* save energy if it's already a pair *)
	| PAIR(pos,x,y) -> (x,y)
	| p -> 
	    let pos = get_pos_lf p in
	    CAN(pos,PR1 p), CAN(pos, PR2 p)
       ) in
      let x = type_check None pos env x a in
      let y = type_check None pos env y (subst_type (w,x) b) in
      PAIR(pos,x,y)

  | e, _  ->
      let (e,s) = type_synthesis env e in 
      subtype env s t;
      e

(* 
  Local Variables:
  compile-command: "ocamlbuild -cflags -g,-annot lfcheck.cmo "
  End:
 *)
