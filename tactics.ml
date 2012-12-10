(** Tactics. *)

open Printf

open Error
open Variables
open Typesystem
open Names
open Tau
open Printer

let add_tactic name f =
  Lfcheck.tactics := (name,f) :: !Lfcheck.tactics

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t =
  let rec repeat = function
    | (v,u) :: envp ->
	if 
	  try Lfcheck.type_equivalence env t u; true
	  with 
	  | TypeCheckingFailure _
	  | TypeCheckingFailure2 _
	  | TypeCheckingFailure3 _ -> false
	then Some(var_to_lf v)
	else repeat envp
    | [] -> None
  in repeat env

(** fill in the third argument of [ev](f,x,_) using tau *)
let ev3 surr env pos t =
  (* This code was formerly a part of the file fillin.ml, removed. *)
  match surr with 
  | Some(_, (pos,APPLY( O O_ev, [CAN f;_;_] ))) -> (
      let tf = tau env f in
      match unmark tf with
      | APPLY(T T_Pi, [_;t]) -> Some t
      | _ -> raise (TypeCheckingFailure(
		    env,
		    get_pos f,
		    "expected a TS function:\n    " ^ ts_expr_to_string f ^
		    "\n  : "^ts_expr_to_string tf)))
  | Some(i,e) ->
      printf "ev3 ( %d , %a ) ?\n" i p_expr (CAN e); flush stdout;
      raise Internal
  | None -> 
      printf "%a: ev3 ?\n" p_pos pos;
      raise Internal

let _ = 
  add_tactic "ev3" ev3;
  add_tactic "assumption" assumption;
  add_tactic "a" assumption

(* 
  Local Variables:
  compile-command: "make tactics.cmo "
  End:
 *)
