(** Tactics. *)

open Printf

open Error
open Variables
open Typesystem
open Names
open Tau
open Printer
open Lfcheck

let add_tactic name f = tactics := (name,f) :: !tactics

(** find the first variable in the context of the right type and return it *)
let assumption surr env pos t args =
  let rec repeat = function
    | (v,u) :: envp ->
	if 
	  try Lfcheck.type_equivalence env t u; true
	  with 
	  | TypeCheckingFailure _
	  | TypeCheckingFailure2 _
	  | TypeCheckingFailure3 _ -> false
	then TacticSuccess(var_to_lf v)
	else repeat envp
    | [] -> TacticFailure
  in repeat env

(** fill in the third argument of [ev](f,x,_) using tau *)
let ev3 surr env pos t args =
  (* This code was formerly a part of the file fillin.ml, removed. *)
  match surr with 
  | Some(_, (pos,EVAL( O O_ev, ARG(f,_)))) -> (
      let tf = tau env f in
      match unmark tf with
      | EVAL(T T_Pi, ARG(_,ARG(t,END))) -> TacticSuccess t
      | _ -> raise (TypeCheckingFailure(
		    env,
		    get_pos f,
		    "expected a TS function:\n    " ^ ts_expr_to_string f ^
		    "\n  : "^ts_expr_to_string tf)))
  | Some(i,e) ->
      printf "ev3 ( %d , %a ) ?\n" i _e (e); flush stdout;
      raise Internal
  | None -> 
      printf "%a: ev3 ?\n" _pos pos;
      raise Internal

(** a tactic that tells the type checker to defer further type checking until
    the next pass, unless it returns something *)
let defer surr env pos t args = TacticDefer(t,args)

let _ = 
  add_tactic "ev3" ev3;
  add_tactic "a" assumption;
  add_tactic "defer" defer

(* 
  Local Variables:
  compile-command: "make tactics.cmo "
  End:
 *)
