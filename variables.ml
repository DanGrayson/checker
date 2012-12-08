(** Variables. *)

open Error

type var =
  | Var of string
  | VarGen of int * string
  | VarUnused
  | VarDefined of string * int

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ (string_of_int i)
  | VarUnused -> "_"
  | VarDefined (name,aspect) -> "[" ^ name ^ "." ^ (string_of_int aspect) ^ "]"

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr;
    if !genctr = genctr_trap then raise DebugMe;
    if !genctr < 0 then raise GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
  | VarDefined _ -> raise Internal
  | VarUnused -> raise Internal
  | Var x | VarGen(_,x) -> newgen x

let newunused () = newfresh (Var "_")
