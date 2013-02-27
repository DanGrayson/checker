(** Variables. *)

open Error

type var =
  | Var of string
  | VarGen of int * string
  | Var_wd of string			(* variables come in pairs, with the *_wd version being the witness twin *)
  | VarGen_wd of int * string
  | VarRel of int			(* deBruijn index, starting with 0 *)

module VarOrd = struct			(* for use with Map.Make *)
  type t = var
  let compare u v = match u,v with	(* this is not a total ordering, because the map will handle only declarations of global variables *)
    | Var a, Var b -> String.compare a b
    | Var_wd a, Var_wd b -> String.compare a b
    | Var _, Var_wd _ -> -1
    | Var_wd _, Var _ ->  1
    | _ -> raise Internal
end

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ string_of_int i
  | Var_wd x -> x ^ "$"
  | VarGen_wd(i,x) -> x ^ "$$" ^ string_of_int i
  | VarRel i -> string_of_int i ^ "^"	(* will not normally appear *)

let base_var = function
  | Var_wd x -> Var x
  | VarRel i -> if i mod 2 = 1 then VarRel (i-1) else raise Internal
  | VarGen_wd _ | Var _ | VarGen _ -> raise Internal

let witness_var = function
  | Var x -> Var_wd x
  | VarRel i -> if i mod 2 = 0 then VarRel (i+1) else raise Internal
  | VarGen(i,x) -> VarGen_wd(i,x)
  | Var_wd _ | VarGen_wd _ -> raise Internal

exception GensymCounterOverflow

let isunused v = 			(* anything using this is likely to be wrong in the presence of tactics *)
  match v with
  | Var id | VarGen(_,id)
  | Var_wd id | VarGen_wd(_,id) -> id = "_"
  | VarRel _ -> raise Internal

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
  | VarRel _ -> raise Internal

let newunused () = VarGen (next_genctr(), "_")

let newunused_wd () = VarGen_wd (next_genctr(), "_")

(* 
  Local Variables:
  compile-command: "make -C .. src/variables.cmo "
  End:
 *)
