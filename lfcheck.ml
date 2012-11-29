(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper:

    Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676–722.
*)

open Typesystem

let rec type_validity (env:environment_type) (pos:Error.position) (t:lftype) : bool =
  match t with 
  | F_Pi(v,t,u) -> type_validity env pos t && type_validity ((LF_Var v,t) :: env) pos u
  | F_APPLY(head,args) ->
      let kind = tfhead_to_kind head in
      let rec repeat env pos kind args = 
	match kind, args with 
	| K_type, [] -> true
	| K_type, x :: args -> false 		(* too many arguments *)
	| K_Pi(v,a,b), x :: args -> type_check env pos x a && repeat ((LF_Var v,a) :: env) pos kind args
	| K_Pi _, [] -> false		(* not enough arguments *)
      in repeat env pos kind args
  | F_Singleton(x,t) -> 
      type_check env pos x t
  | F_hole -> false

and check_subtype (env:environment_type) (pos:Error.position) (t:lftype) (u:lftype) : bool =
  raise Error.NotImplemented

and type_equivalence (env:environment_type) (pos:Error.position) (t:lftype) (u:lftype) : bool =
  raise Error.NotImplemented

and term_equivalence (env:environment_type) (pos:Error.position) (x:expr) (y:expr) (t:lftype) : bool =
  raise Error.NotImplemented

and path_equivalence (env:environment_type) (pos:Error.position) (x:expr) (y:expr) : lftype option =
  raise Error.NotImplemented

and type_synthesis (env:environment_type) (pos:Error.position) (e:expr) : lftype option =
  match e with
  | POS(pos,e) -> (
      match e with
      | Variable v -> 
	  raise Error.NotImplemented
      | EmptyHole i -> 
	  raise Error.NotImplemented
      | APPLY(label,args) ->
	  raise Error.NotImplemented
	    )
  | LAMBDA(v,e) ->
	  raise Error.NotImplemented

and type_check (env:environment_type) (pos:Error.position) (e:expr) (t:lftype) : bool = 
  match type_synthesis env pos e with
    Some u -> check_subtype env pos t u
  | None -> false


(* 
  Local Variables:
  compile-command: "ocamlbuild lfcheck.cmo "
  End:
 *)
