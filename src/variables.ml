(** Variables. *)

open Error

type var =
  | Var of string
  | VarGen of int * string
  | Var_wd of int			(* we represent [wd_i] as (Var_wd i) *)

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ string_of_int i
  | Var_wd i -> "[wd_" ^ string_of_int i ^ "]"

exception GensymCounterOverflow

let isunused v = 
  match v with
  | Var id | VarGen(_,id) -> id = "_"
  | Var_wd _ -> false

let next_genctr = 
  let genctr = ref 0 in
  fun () -> incr genctr; 
    if !genctr < 0 then raise GensymCounterOverflow;
    if !genctr = genctr_trap then trap();
    if !genctr = genctr_exception then (trap(); raise DebugMe); 
    !genctr

let newfresh = function
  | Var x | VarGen(_,x) -> (
      assert(x <> "_");
      VarGen (next_genctr(), x))
  | Var_wd _ -> raise Internal

let newunused () = VarGen (next_genctr(), "_")

(* 
  Local Variables:
  compile-command: "make -C .. src/error.cmo "
  End:
 *)
