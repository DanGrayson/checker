(** Variables. *)

open Error

type var =
  | Var of string
  | VarGen of int * string
  | Var_wd of string			(* variables come in pairs, with the *_wd version being the witness twin *)
  | VarGen_wd of int * string

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ string_of_int i
  | Var_wd x -> x ^ "$"
  | VarGen_wd(i,x) -> x ^ "$$" ^ string_of_int i

let base_var = function
  | Var_wd x -> Var x
  | VarGen_wd _ | Var _ | VarGen _ -> raise Internal

let witness_var = function
  | Var x -> Var_wd x
  | VarGen _ | Var_wd _ | VarGen_wd _ -> raise Internal

exception GensymCounterOverflow

let isunused v = 			(* anything using this is likely to be wrong in the presence of tactics *)
  match v with
  | Var id | VarGen(_,id)
  | Var_wd id | VarGen_wd(_,id) -> id = "_"

let next_genctr = 
  let genctr = ref 0 in
  fun () -> incr genctr; 
    if !genctr < 0 then raise GensymCounterOverflow;
    if !genctr = genctr_trap then trap();
    if !genctr = genctr_exception then (trap(); raise DebugMe); 
    !genctr

let newfresh = function
  | Var x | VarGen(_,x) -> (
      VarGen (next_genctr(), x))
  | Var_wd x | VarGen_wd(_,x) -> (
      VarGen_wd (next_genctr(), x))

let newunused () = VarGen (next_genctr(), "_")

let newunused_wd () = VarGen_wd (next_genctr(), "_")

(* 
  Local Variables:
  compile-command: "make -C .. src/error.cmo "
  End:
 *)
