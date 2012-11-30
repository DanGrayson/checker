(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676–722.
*)

open Typesystem
open Error
open Printer

exception TypingError of position * string

let err pos msg = raise (TypingError (pos, msg))

let err2 pos msg pos' msg' = raise (TypeCheckingFailure2 (pos, msg, pos', msg'))

let mismatch_type pos t pos' t' = raise (TypeCheckingFailure2 (
				    pos , "expected type "^(lf_type_to_string t ),
				    pos', "to match      "^(lf_type_to_string t')))

let mismatch_term pos x pos' x' = raise (TypeCheckingFailure2 (
				    pos , "expected term "^(lf_canonical_to_string x ),
				    pos', "to match      "^(lf_canonical_to_string x')))

let rec strip_singleton ((_,(_,t)) as u) = match t with
| F_Singleton a -> strip_singleton a
| _ -> u

(* background assumption: all types in the environment have been verified *)

let rec natural_type (x:lf_expr) : lf_type =
  (* see figure 9 page 696 *)
  raise NotImplemented

let rec head_reduction (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 *)
  raise NotImplemented

let rec head_normalization (x:lf_expr) : lf_expr =
  (* see figure 9 page 696 *)
  raise NotImplemented

let rec type_validity (env:context) (t:lf_type) : unit =
  (* assume the kinds of constants, and the types in them, have been checked *)
  (* driven by syntax *)
  (* see figure 12, page 715 *)
  let (pos,t) = t in
  match t with 
  | F_Pi(v,t,u) -> 
      type_validity env t;
      type_validity ((LF_Var v,t) :: env) u
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let rec repeat env kind (args:lf_expr list) = 
	match kind, args with 
	| K_type, [] -> ()
	| K_type, x :: args -> err pos "at least one argument too many"
	| K_Pi(v,a,kind'), x :: args ->
	    type_check pos env x a;
	    repeat ((LF_Var v,a) :: env) kind' args
	| K_Pi(_,a,_), [] -> err pos ("too few arguments; next argument should be of type "^(lf_type_to_string a))
      in repeat env kind args
  | F_Singleton(x,t) -> 
      type_validity env t;
      type_check pos env x t		(* rule 46 *)

and type_synthesis (env:context) (e:ts_expr) : lf_type =
  (* assume nothing *)
  (* see figure 13, page 716 *)
  let (pos,e) = e in
     match e with
     | Variable v -> (
	 try (pos, F_Singleton(ATOMIC(pos,e), (List.assoc (LF_Var v) env)))
	 with Not_found -> err pos "unbound variable"
	)
     | EmptyHole _ -> err pos "empty hole"
     | APPLY(label,args) ->
	 with_pos pos 				(* the position of the type will reflect the position of the expression *)
	   (strip_pos (
	    let a = 
	      try label_to_lf_type env label
	      with Not_found -> err pos ("unbound variable: "^(label_to_string label))
	    in
	    let rec repeat env (a:lf_type) (args:lf_expr list) : lf_type = (
	      let (apos,a0) = a in
	      match a0, args with
	      | F_APPLY _ as t, [] -> (pos,t)
	      | F_Singleton(e,t), args -> repeat env t args
	      | F_Pi(v,a,_), [] -> 
		  err pos ("too few arguments; next argument should be of type "^(lf_type_to_string a))
	      | F_Pi(x,a',a''), m' :: args' ->
		  type_check pos env m' a';
                  repeat ((LF_Var x,a') :: env) (Substitute.subst_type [ (x,m') ] a'') args'
	      | F_APPLY _, ATOMIC (pos,_) :: _ -> err pos "extra argument"
	      | F_APPLY _, LAMBDA _ :: _ -> err pos "extra argument"
	     )
	    in repeat env a args))

and term_equivalence (xpos:position) (ypos:position) (env:context) (x:lf_expr) (y:lf_expr) (t:lf_type) : unit =
  (* assume x and y have already been verified to be of type t *)
  (* see figure 11, page 711 *)
  if x = y then ()
  else (
    let (pos,t0) = t in
    match x, y, t0 with
    | _, _, F_Singleton _ -> ()
    | _ -> 
	mismatch_term xpos x ypos y
   )

and path_equivalence (env:context) (x:ts_expr) (y:ts_expr) : lf_type =
  (* assume nothing *)
  (* see figure 11, page 711 *)
  if x = y then type_synthesis env x
  else
  raise NotImplemented

and type_equivalence (env:context) (t:lf_type) (u:lf_type) : unit =
  (* see figure 11, page 711 *)
  (* assume t and u have already been verified to be types *)
  if t = u then ()
  else
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  if t0 = u0 then ()
  else 
  match t0, u0 with
  | F_Singleton a, F_Singleton b ->
      let (x,t) = strip_singleton a in
      let (y,u) = strip_singleton b in
      type_equivalence env t u;
      term_equivalence tpos upos env x y t
  | F_Pi(v,a,b), F_Pi(w,c,d) ->
      type_equivalence env a c;
      type_equivalence ((LF_Var v, a) :: env) b (Substitute.subst_type [(w, ATOMIC (Nowhere,Variable v))] d)
  | F_APPLY(h,args), F_APPLY(h',args') ->
      if not (h = h') then mismatch_type tpos t upos u;
      let k = tfhead_to_kind h in
      let rec repeat (k:lf_kind) args args' : unit =
	match k,args,args' with
        | K_Pi(v,t,k), x :: args, x' :: args' ->
            term_equivalence tpos upos env x x' t;
            repeat (Substitute.subst_kind [(v,x)] k) args args'
        | K_type, [], [] -> ()
	| _ -> raise Internal
      in repeat k args args';
      raise Internal
  | F_APPLY _, F_Pi _
  | F_Pi _, F_APPLY _ -> mismatch_type tpos t upos u
  | _ -> raise Internal

and subtype (env:context) (t:lf_type) (u:lf_type) : unit =
  (* assume t and u have already been verified to be types *)
  (* driven by syntax *)
  (* see figure 12, page 715 *)
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  match t0, u0 with
  | F_Singleton a, F_Singleton b ->
      let (x,t) = strip_singleton a in
      let (y,u) = strip_singleton b in
      type_equivalence env t u;
      term_equivalence tpos upos env x y t
  | _, F_Singleton _ -> err tpos "expected a singleton type"
  | F_Singleton a, _ -> 
      let (x,t) = strip_singleton a in
      type_equivalence env t u
  | F_Pi(x,a,b) , F_Pi(y,c,d) ->
      subtype env c a;			(* contravariant *)
      subtype ((LF_Var x, a) :: env) b d
  | _ -> type_equivalence env (tpos,t0) (upos,u0)

and type_check (pos:position) (env:context) (e:lf_expr) (t:lf_type) : unit = 
  (* assume t has been verified to be a type *)
  (* see figure 13, page 716 *)
  let (_,t0) = t in 
  match e, t0 with
  | LAMBDA(v,e), F_Pi(w,a,b) ->
      type_check pos ((LF_Var (strip_pos v),a) :: env) e (Substitute.subst_type [(w,ATOMIC (with_pos (get_pos v) (Variable (strip_pos v))))] b)
  | LAMBDA _, _ -> err pos "did not expect a lambda expression here"
  | ATOMIC e, _ -> let s = type_synthesis env e in subtype env s t

(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
