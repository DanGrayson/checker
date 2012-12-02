(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    [EEST]: Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676-722.
*)

open Typesystem
open Error
open Printer
open Substitute
open Printf

let try_alpha = false (* turning this on could slow things down a lot before we implement hash codes *)

let err env pos msg = raise (TypeCheckingFailure (env, pos, msg))

let errmissingarg env pos a = err env pos ("missing next argument, of type "^(lf_type_to_string a))

let mismatch_type env pos t pos' t' = 
  raise (TypeCheckingFailure2 (env,
	 pos , "expected type "^(lf_type_to_string t ),
	 pos', "to match      "^(lf_type_to_string t')))

let mismatch_term_t env pos x pos' x' t = 
  raise (TypeCheckingFailure3 (env,
		    pos , "expected term\n\t"^(lf_canonical_to_string x ),
		    pos',      "to match\n\t"^(lf_canonical_to_string x'),
	       get_pos t,       "of type\n\t"^(lf_type_to_string t)))

let mismatch_term env pos x pos' x' = 
  raise (TypeCheckingFailure2 (env,
		    pos , "expected term\n\t"^(lf_canonical_to_string x ),
		    pos',      "to match\n\t"^(lf_canonical_to_string x')))

let rec strip_singleton ((_,(_,t)) as u) = match t with
| F_Singleton a -> strip_singleton a
| _ -> u

(* background assumption: all types in the environment have been verified *)

let unfold env v =
  match unmark( lookup_type env v ) with
  | F_Singleton a -> let (x,t) = strip_singleton a in x
  | _ -> raise Not_found

let rec natural_type (pos:position) (env:context) (x:lf_expr) : lf_type =
  (* assume nothing *)
  (* see figure 9 page 696 [EEST] *)
  match x with
  | CAN (pos,x) -> (
      match x with
      | EmptyHole _ -> err env pos "empty hole found"
      | APPLY(l,args) -> 
          let t =
            try label_to_lf_type env l
            with Not_found -> err env pos ("unbound variable: "^(label_to_string l)) in
          let rec repeat args t =
            match args, unmark t with
	    | x :: args, F_Pi(v,a,b) -> repeat args (subst_type (v,x) b)
	    | x :: args, _ -> err env pos "at least one argument too many"
	    | [], F_Pi(v,a,b) -> errmissingarg env pos a (* we insist on eta-long format *)
	    | [], t -> t
	  in nowhere 5 (repeat args t))
  | LAMBDA _ -> err env pos "LF lambda expression found, has no natural type"

let rec head_reduction (env:context) (x:lf_expr) : lf_expr =
  (* assume nothing *)
  (* see figure 9 page 696 [EEST] *)
  (* may raise Not_found if there is no head reduction *)
  match x with
  | CAN (pos,x) -> (
      match x with
      | EmptyHole _ -> err env pos "empty hole found"
      | APPLY(V v, args) -> (
	  let f = unfold env v in
	  let rec repeat f args = 
	    match f with
	    | LAMBDA(v,body) -> (
		match args with
		| x :: args -> repeat (subst' (v,x) body) args
		| [] -> err env pos "too few arguments")
	    | x -> (
		match args with
		| [] -> x
		| _ -> err env pos "too many arguments")
	  in repeat f args)
      | APPLY _ -> raise Not_found)
  | LAMBDA _ -> raise Not_found

let rec head_normalization (env:context) (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 [EEST] *)
  try let r = head_normalization env (head_reduction env x) in r
  with Not_found -> x

let rec type_validity (env:context) (t:lf_type) : unit =
  (* assume the kinds of constants, and the types in them, have been checked *)
  (* driven by syntax *)
  (* see figure 12, page 715 [EEST] *)
  let (pos,t) = t in
  match t with 
  | F_Pi(v,t,u) -> 
      type_validity env t;
      type_validity ((v,t) :: env) u
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let rec repeat env kind (args:lf_expr list) = 
	match kind, args with 
	| K_type, [] -> ()
	| K_type, x :: args -> err env pos "at least one argument too many"
	| K_Pi(v,a,kind'), x :: args ->
	    type_check pos env x a;
	    repeat ((v,a) :: env) kind' args
	| K_Pi(_,a,_), [] -> errmissingarg env pos a
      in repeat env kind args
  | F_Singleton(x,t) -> 
      type_validity env t;
      type_check pos env x t		(* rule 46 *)

and type_synthesis (env:context) (e:ts_expr) : lf_type =
  (* assume nothing *)
  (* see figure 13, page 716 [EEST] *)
  let (pos,e0) = e in
     match e0 with
     | EmptyHole _ -> err env pos ("empty hole: "^(lf_atomic_to_string e))
     | APPLY(V v, []) -> (
	 try (pos, F_Singleton(CAN e, (List.assoc v env)))
	 with Not_found -> 
	   err env pos ("unbound variable: "^(vartostring v))
	)
     | APPLY(label,args) ->
	 with_pos pos 				(* the position of the type will reflect the position of the expression *)
	   (unmark (
	    let a = 
	      try label_to_lf_type env label
	      with Not_found -> raise Internal (* covered in the case above *)
	    in
	    let rec repeat env (a:lf_type) (args:lf_expr list) : lf_type = (
	      let (apos,a0) = a in
	      match a0, args with
	      | F_APPLY _ as t, [] -> (pos,t)
	      | F_Singleton(e,t), args -> repeat env t args
	      | F_Pi(v,a,_), [] -> 
		  err env pos ("too few arguments; next argument should be of type "^(lf_type_to_string a))
	      | F_Pi(x,a',a''), m' :: args' ->
		  type_check pos env m' a';
                  repeat ((x,a') :: env) (subst_type (x,m') a'') args'
	      | F_APPLY _, CAN (pos,_) :: _ -> err env pos "extra argument"
	      | F_APPLY _, LAMBDA _ :: _ -> err env pos "extra argument"
	     )
	    in repeat env a args))

and term_equivalence (xpos:position) (ypos:position) (env:context) (x:lf_expr) (y:lf_expr) (t:lf_type) : unit =
  (* assume x and y have already been verified to be of type t *)
  (* see figure 11, page 711 [EEST] *)
  let try_path_equivalence x y =
    let x = head_normalization env x in (* not mentioned in the paper (?) *)
    let y = head_normalization env y in (* not mentioned in the paper (?) *)
    let t' = path_equivalence env x y in
    type_equivalence env t t' in
  if try_alpha && Alpha.UEqual.term_equiv empty_uContext x y then () else
  let (pos,t0) = t in
  match x, y, t0 with
  | _, _, F_Singleton _ -> ()
  | x, y, F_Pi (w,a,b) -> (
      let x = head_normalization env x in (* not mentioned in the paper (?) *)
      let y = head_normalization env y in (* not mentioned in the paper (?) *)
      match x,y with
      | LAMBDA(u,x), LAMBDA(v,y) ->
	  let w' = newfresh w in
	  term_equivalence xpos ypos ((w',a) :: env) (* all this variable substitution should be handled by alpha equivalence in the future *)
	    (subst' (u,var_to_lf w') x)
	    (subst' (v,var_to_lf w') y)
	    (subst_type (w,var_to_lf w') b)
      | x,y -> try_path_equivalence x y
     )
  | x, y, F_APPLY(j,args) -> try_path_equivalence x y

and path_equivalence (env:context) (x:lf_expr) (y:lf_expr) : lf_type =
  (* assume x and y are head reduced *)
  (* see figure 11, page 711 [EEST] *)
  match x,y with
  | CAN (xpos,x0), CAN (ypos,y0) -> (
      match x0,y0 with
      | APPLY(f,args), APPLY(f',args') ->
          if not (f = f') 
	  then mismatch_term env xpos x ypos y;
          let t = 
	    try label_to_lf_type env f 
	    with Not_found -> err env xpos ("unbound variable: "^(label_to_string f)) in
          let rec repeat t args args' =
            match t,args,args' with
            | t, [], [] -> t
            | (pos,F_Pi(v,a,b)), x :: args, y :: args' ->
                term_equivalence xpos ypos env x y a;
                repeat (subst_type (v,x) b) args args'
            | _ -> mismatch_term env xpos x ypos y
	  in repeat t args args'
      | _ -> mismatch_term env xpos x ypos y)
  | _  -> mismatch_term env (get_pos_can x) x (get_pos_can y) y

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
  | F_Pi(v,a,b), F_Pi(w,c,d) ->
      type_equivalence env a c;
      if v = VarUnused && w = VarUnused
      then type_equivalence env b d
      else
	let x = newfresh (Var "te") in
	type_equivalence ((x, a) :: env)
	  (subst_type (v, var_to_lf x) b)
	  (subst_type (w, var_to_lf x) d)
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
      subtype ((x, a) :: env) b d
  | _ -> type_equivalence env (tpos,t0) (upos,u0)

and type_check (pos:position) (env:context) (e:lf_expr) (t:lf_type) : unit = 
  (* assume t has been verified to be a type *)
  (* see figure 13, page 716 [EEST] *)
  let (_,t0) = t in 
  match e, t0 with
  | LAMBDA(v,e), F_Pi(w,a,b) ->
      type_check pos 
	((v,a) :: env)
	e
	(subst_type (w,var_to_lf v) b)
  | LAMBDA _, _ -> err env pos "did not expect a lambda expression here"
  | CAN (pos, EmptyHole n), _ -> 
      raise (TypeCheckingFailure2 (env,
	 pos, "hole found : "^(lf_canonical_to_string e),
	 pos, "   of type : "^(lf_type_to_string t)))
  | CAN e, _ -> let s = type_synthesis env e in subtype env s t

(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
