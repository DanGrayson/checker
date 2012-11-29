(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676–722.
*)

open Typesystem

exception TypingError of Error.position * string

let rec type_validity (env:environment_type) (t:lf_type) : unit =
  (* driven by syntax *)
  let (pos,t) = t in
  match t with 
  | F_Pi(v,t,u) -> 
      type_validity env t;
      type_validity ((LF_Var v,t) :: env) u
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let rec repeat env kind args = 
	match kind, args with 
	| K_type, [] -> ()
	| K_type, x :: args -> raise (TypingError (get_pos x, "at least one argument too many"))
	| K_Pi(v,a,kind'), x :: args ->
	    type_validity env a;	(*?*)
	    type_check env x a;
	    repeat ((LF_Var v,a) :: env) kind' args
	| K_Pi _, [] -> raise (TypingError (pos, "too few arguments"))
      in repeat env kind args
  | F_Singleton(x,t) -> 
      type_validity env t;
      type_check env x t		(* rule 46 *)
  | F_hole -> 
      raise (TypingError (pos, "empty LF type hole"))

and type_check (env:environment_type) (e:ts_expr) (t:lf_type) : unit = 
  match e, t with
  | LAMBDA(v,e), F_Pi(w,a,b) ->
      type_check ((LF_Var (strip_pos v),a) :: env) e (Substitute.subst_type [(w,nowhere (Variable (strip_pos v)))] b)
  | _ -> let s = type_synthesis env e in subtype env s t

and subtype (env:environment_type) (t:lf_type) (u:lf_type) : unit =
  (* driven by syntax *)
  (* see figure 12, page 715 *)
  let (tpos,t) = t in 
  let (upos,u) = u in 
  if t = u then ()
  else 
  match t, u with
  | F_Singleton(x,t), F_Singleton(y,u) ->
      subtype env t u;
      term_equivalence env x y t		(* rule 45 *)
  | F_Singleton(x,t), u ->
      subtype env t u;
      type_check env x t		(* rule 44 *)
  | F_Pi(x,a,b) , F_Pi(y,c,d) ->
      subtype env a c;
      subtype ((LF_Var x, a) :: env) b d
  | F_APPLY(h1, args1) , F_APPLY(h2, args2) ->
      if not (h1 = h2) then (
	raise (TypingError (pos, "unequal judgment types"))
       );
      raise Error.NotImplemented
  | _ -> raise (TypingError (pos, "unequal types"));

and type_equivalence (env:environment_type) (t:lf_type) (u:lf_type) : unit =
  raise Error.NotImplemented

and term_equivalence (env:environment_type) (x:ts_expr) (y:ts_expr) (t:lf_type) : unit =
  if x = y then ()
  else (
    type_check env x t;
    type_check env y t;
    match x, y, t with
    | x, y, F_Singleton(z,u) ->
	term_equivalence env x z u;
	term_equivalence env y z u	(* rule 43, sort of *)
    | _ -> raise Error.NotImplemented)

and path_equivalence (env:environment_type) (x:ts_expr) (y:ts_expr) : lf_type =
  if x = y then type_synthesis env x
  else
  raise Error.NotImplemented

and type_synthesis (env:environment_type) (e:ts_expr) : lf_type =
  match e with
  | ATOMIC(pos,e') -> (
      match e' with
      | Variable v -> (
	  try List.assoc (LF_Var v) env (* F_Singleton(e, (List.assoc (LF_Var v) env)) ?? *)
	  with Not_found -> raise (TypingError (pos, "unbound variable"))
	 )
      | EmptyHole _ -> raise (TypingError (pos, "empty hole"))
      | APPLY(label,args) ->
	  let a = label_to_lf_type env label in
	  let rec repeat env a args = (
	    match a, args with
	    | F_Pi _, [] -> raise (TypingError (pos, "too few arguments"))		
	    | a, [] -> a			(* that's the answer *)
	    | F_Pi(x,a',a''), m' :: args' ->
		type_check env m' a';
		repeat ((LF_Var x,a') :: env) (Substitute.subst_type [(x,m')] a'') args'
	    | _ -> 
		raise Error.NotImplemented)
	  in repeat env a args
	 )
  | LAMBDA(v,e) -> raise (TypingError (pos, "isolated LF lambda expression"))

(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
