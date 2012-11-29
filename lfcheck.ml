(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676–722.
*)

open Typesystem

let rec type_validity (env:environment_type) (pos:Error.position) (t:lftype) : bool =
  (* driven by syntax *)
  match t with 
  | F_Pi(v,t,u) -> 
      type_validity env pos t && type_validity ((LF_Var v,t) :: env) pos u
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let rec repeat env pos kind args = 
	match kind, args with 
	| K_type, [] -> true
	| K_type, x :: args -> false	(* too many arguments *)
	| K_Pi(v,a,kind'), x :: args ->
	    type_validity env pos a	(*?*)
	      &&
	    type_check env pos x a
	      && 
	    repeat ((LF_Var v,a) :: env) pos kind' args
	| K_Pi _, [] -> false		(* not enough arguments *)
      in repeat env pos kind args
  | F_Singleton(x,t) -> 
      type_validity env pos t
	&&
      type_check env pos x t		(* rule 46 *)
  | F_hole -> 
      false			(* unfilled hole; usually just unimplemented code *)

and type_check (env:environment_type) (pos:Error.position) (e:expr) (t:lftype) : bool = 
  Printf.printf "  type_check  e = %s   t = %s\n" (Printer.lfexpr_to_string e) (Printer.lftype_to_string true t);
  match e, t with
  | LAMBDA(v,e), F_Pi(w,a,b) ->
      type_check ((LF_Var (strip_pos_var v),a) :: env) pos e (Substitute.subst_type [(w,nowhere (Variable (strip_pos_var v)))] b)
  | _ ->
      match type_synthesis env pos e with
	Some s -> subtype env pos s t
      | None -> false

and subtype (env:environment_type) (pos:Error.position) (t:lftype) (u:lftype) : bool =
  (* driven by syntax *)
  (* see figure 12, page 715 *)
  t = u
  ||
  match t, u with
  | F_Singleton(x,t), F_Singleton(y,u) ->
      subtype env pos t u
	&&
      term_equivalence env pos x y t		(* rule 45 *)
  | F_Singleton(x,t), u ->
      subtype env pos t u
	&&
      type_check env pos x t		(* rule 44 *)
  | F_Pi(x,a,b) , F_Pi(y,c,d) ->
      subtype env pos a c
	&&
      subtype ((LF_Var x, a) :: env) pos b d
  | F_APPLY(h1, args1) , F_APPLY(h2, args2) ->
      h1 = h2
	&&
      raise Error.NotImplemented
  | _ -> 
      Printf.fprintf stderr "--- not a subtype : t = %s   u = %s\n" (Printer.lftype_to_string true t) (Printer.lftype_to_string true u);
      false

and type_equivalence (env:environment_type) (pos:Error.position) (t:lftype) (u:lftype) : bool =
  raise Error.NotImplemented

and term_equivalence (env:environment_type) (pos:Error.position) (x:expr) (y:expr) (t:lftype) : bool =
  x = y
    &&
  type_check env pos x t
    &&
  type_check env pos y t
  ||
  match x, y, t with
  | x, y, F_Singleton(z,u) ->
      term_equivalence env pos x z u
	&&
      term_equivalence env pos y z u	(* rule 43, sort of *)
  | _ -> raise Error.NotImplemented

and path_equivalence (env:environment_type) (pos:Error.position) (x:expr) (y:expr) : lftype option =
  if x = y then type_synthesis env pos x
  else
  raise Error.NotImplemented

and type_synthesis (env:environment_type) (pos:Error.position) (e:expr) : lftype option =
  Printf.printf " type_synthesis   e = %s\n" (Printer.lfexpr_to_string e);
  match e with
  | POS(pos,e') -> (
      match e' with
      | Variable v -> (
	  try
	    (* Some (F_Singleton(e, (List.assoc (LF_Var v) env))) ?? *)
	    Some (List.assoc (LF_Var v) env)
	  with Not_found -> None
	 )
      | EmptyHole _ -> None
      | APPLY(label,args) ->
	  let a = label_to_lftype label in
	  let rec repeat env pos a args = (
	    match a, args with
	    | F_Pi _, [] -> None		(* not enough arguments *)
	    | a, [] -> Some a			(* that's the answer *)
	    | F_Pi(x,a',a''), m' :: args' ->
		Printf.printf " m' = %s   a' = %s\n" (Printer.lfexpr_to_string m') (Printer.lftype_to_string true a');
		if type_check env pos m' a'
		then 
		  repeat ((LF_Var x,a') :: env) pos (Substitute.subst_type [(x,m')] a'') args'
		else None
	    | _ -> 
		Printf.printf " a = %s" (Printer.lftype_to_string true a);
		List.iter (fun arg -> Printf.printf "    arg = %s\n" (Printer.lfexpr_to_string arg)) args;
		raise Error.NotImplemented)
	  in repeat env pos a args
	 )
  | LAMBDA(v,e) -> None

(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
