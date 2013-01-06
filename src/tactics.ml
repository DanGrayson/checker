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
let assumption surr env pos t =
  let rec repeat = function
    | (v,u) :: envp -> (
	try
	  Lfcheck.type_equivalence env t u;
	  TacticSuccess(var_to_lf v)
	with TypeEquivalenceFailure -> 
	  repeat envp)
    | [] -> TacticFailure
  in repeat env

(** fill in the third argument of [ev](f,x,_) using tau *)
let ev3 (surr:surrounding) env pos t =
  (* This code was formerly a part of the file fillin.ml, removed. *)
  match surr with 
  | (_, (pos,APPLY( O O_ev, ARG(f,_))), _) :: _ -> (
      try
	let tf = 
	  tau env f 
	in (
	match unmark tf with
	| APPLY(T T_Pi, ARG(_,ARG(t,END))) -> TacticSuccess t
	| _ -> raise (TypeCheckingFailure(
		      env, surr, [
		      get_pos f,
		      "expected a TS function:\n    " ^ ts_expr_to_string f ^
		      "\n  : " ^ ts_expr_to_string tf ])))
	  
      with NotImplemented ->
	printf "warning: ev3: \"tau\" not implemented for %a\n%!" _e f;
	TacticFailure)
  | (i,e,t) :: _ ->
      let i = match i with Some i -> i | None -> -1 in
      printf "ev3 ( %d , %a ) ?\n%!" i _e (e);
      internal ()
  | [] -> 
      printf "%a: ev3 ?\n%!" _pos pos;
      internal ()

let rec default surr env pos t = 
  match unmark t with
  | F_Singleton(e,_) -> TacticSuccess e
  | F_Pi(v,a,b) -> (
      match default surr ((v,a) :: env) (get_pos t) b with 
      | TacticSuccess e -> TacticSuccess (with_pos pos (LAMBDA(v,e)))
      | TacticFailure -> TacticFailure)
  | F_Apply((F_hastype|F_istype),_) -> assumption surr env pos t
  | _ -> TacticFailure

let _ = 
  add_tactic "ev3" ev3;
  add_tactic "a" assumption;
  add_tactic "default" default

(* 
  Local Variables:
  compile-command: "make -C .. src/tactics.cmo "
  End:
 *)
