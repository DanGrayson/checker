(** Tactics. *)

open Judgments
open Contexts

type surrounding_component =
  | S_expr_list of int			 (* argument position, starting with 1 *)
  | S_expr_list' of int			 (* argument position, starting with 1 *)
	* expr_head			 (* head *)
	* expr_list			 (* arguments passed, in reverse order, possibly updated by tactics *)
	* expr_list			 (* arguments coming *)
  | S_type_args of int                   (* argument position, starting with 1 *)
	* judgment list			 (* arguments passed, possibly updated by tactics *)
  | S_type_family_args of int            (* argument position, starting with 1 *)
	* expr list			 (* arguments passed, in reverse order, possibly updated by tactics *)
  | S_projection of int
  | S_body

type surrounding = (environment * surrounding_component * expr option * judgment option) list

type tactic_return =
  | TacticFailure
  | TacticSuccess of expr

type tactic_function =
       surrounding         (* the ambient BASIC(...), if any, and the index among its head and arguments of the hole *)
    -> environment						      (* the active context *)
    -> position							      (* the source code position of the tactic hole *)
    -> judgment							      (* the type of the hole, e.g., [texp] *)
    -> expr_list							      (* the arguments *)
 -> tactic_return						      (* the proffered expression *)

let tactics : (string * tactic_function) list ref = ref []

let add_tactic (name,f) = tactics := (name,f) :: !tactics

(*
  Local Variables:
  compile-command: "make -C .. src/typesystem.cmo "
  End:
 *)
