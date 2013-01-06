(** Variables. *)

open Error

type var =
  | Var of string
  | VarGen of int * string

let basename = function
  | Var x -> x
  | VarGen(i,x) -> x

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ string_of_int i

exception GensymCounterOverflow

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr;
    if !genctr = genctr_trap then (trap(); raise DebugMe);
    if !genctr < 0 then raise GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
  | Var x | VarGen(_,x) -> newgen x

let newunused () = newfresh (Var "_")
