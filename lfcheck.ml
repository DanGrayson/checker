(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676–722.
*)

open Typesystem
open Error

exception TypingError of position * string

let err pos msg = raise (TypingError (pos, "did not expect a lambda expression here"))

let rec type_check (pos:position) (env:environment_type) (e:lf_expr) (t:lf_type) : unit = 
  let (_,t0) = t in 
  match e, t0 with
  | LAMBDA(v,e), F_Pi(w,a,b) ->
      type_check pos ((LF_Var (strip_pos v),a) :: env) e (Substitute.subst_type [(w,nowhere (Variable (strip_pos v)))] b)
  | LAMBDA _, _ -> err pos "did not expect a lambda expression here"
  | ATOMIC e, _ -> let s = type_synthesis env e in subtype env s t

and type_validity (env:environment_type) (t:lf_type) : unit =
  (* driven by syntax *)
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
	| K_type, x :: args -> raise (TypingError (pos, "at least one argument too many"))
	| K_Pi(v,a,kind'), x :: args ->
	    type_validity env a;	(*?*)
	    type_check pos env x a;
	    repeat ((LF_Var v,a) :: env) kind' args
	| K_Pi _, [] -> raise (TypingError (pos, "too few arguments"))
      in repeat env kind args
  | F_Singleton(x,t) -> 
      type_validity env t;
      type_check pos env x t		(* rule 46 *)
  | F_hole -> 
      raise (TypingError (pos, "empty LF type hole"))

and type_synthesis (env:environment_type) (e:ts_expr) : lf_type =
  let (pos,e) = e in
  match e with
  | Variable v -> (
      try List.assoc (LF_Var v) env (* F_Singleton(e, (List.assoc (LF_Var v) env)) ?? *)
      with Not_found -> raise (TypingError (pos, "unbound variable"))
     )
  | EmptyHole _ -> raise (TypingError (pos, "empty hole"))
  | APPLY(label,args) ->
      let a = label_to_lf_type env label in
      let rec repeat env (a:lf_type) (args:lf_expr list) : lf_type = (
	let (pos,a0) = a in
	match a0, args with
	| F_Pi _, [] -> raise (TypingError (pos, "too few arguments"))		
	| a, [] -> (pos,a)			(* ??? *)
	| F_Pi(x,a',a''), m' :: args' ->
	    type_check pos env m' a';
	    repeat ((LF_Var x,a') :: env) (Substitute.subst_type [ (* (x,m') *) ] a'') args'
	| _ -> 
	    raise NotImplemented)
      in repeat env a args

and subtype (env:environment_type) (t:lf_type) (u:lf_type) : unit =
  (* driven by syntax *)
  (* see figure 12, page 715 *)
  let (tpos,t0) = t in 
  let (upos,u0) = u in 
  if t0 = u0 then ()
  else 
  match t0, u0 with
  | F_Singleton(x,t), F_Singleton(y,u) ->
      subtype env t u;
      term_equivalence tpos upos env x y t		(* rule 45 *)
  | F_Singleton(x,t), _ ->
      subtype env t u;
      type_check tpos env x t		(* rule 44 *)
  | F_Pi(x,a,b) , F_Pi(y,c,d) ->
      subtype env a c;
      subtype ((LF_Var x, a) :: env) b d
  | F_APPLY(h1, args1) , F_APPLY(h2, args2) ->
      if not (h1 = h2) then (
	raise (TypingError (tpos, "unequal judgment types"))
       );
      raise NotImplemented
  | _ -> raise (TypingError (tpos, "unequal types"));

and type_equivalence (env:environment_type) (t:lf_type) (u:lf_type) : unit =
  raise NotImplemented

and term_equivalence (xpos:position) (ypos:position) (env:environment_type) (x:lf_expr) (y:lf_expr) (t:lf_type) : unit =
  if x = y then ()
  else (
    type_check xpos env x t;
    type_check ypos env y t;
    let (pos,t0) = t in
    match x, y, t0 with
    | _, _, F_Singleton(z,u) ->
	term_equivalence xpos ypos env x z u;
	term_equivalence xpos ypos env y z u	(* rule 43, sort of *)
    | _ -> raise NotImplemented)

and path_equivalence (env:environment_type) (x:ts_expr) (y:ts_expr) : lf_type =
  if x = y then type_synthesis env x
  else
  raise NotImplemented

(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
