open Typesystem

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr; 
    if !genctr < 0 then raise Error.GensymCounterOverflow;
    OVarGen (!genctr, x)) in
  fun v -> match v with 
      OVar x | OVarGen(_,x) -> newgen x
    | OVarUnused as v -> v
    | OVarEmptyHole as v -> v

(** This version substitutes only for o-variables. *)
let rec subst subs =
  let rec substlist es = List.map subst1 es
  and subst1 = function
    | POS(pos,e) -> POS(pos,subst1 e)
    | UU _ as u -> u
    | TT_variable _ as t -> t
    | OO_variable v as o -> (try List.assoc v subs with Not_found -> o)
    | APPLY(label,branches) -> (
      match label with 
      | LAMBDA (pos,v) -> 
	  let v' = newfresh v in
	  let subs = (v,OO_variable v') :: subs in 
	  APPLY(LAMBDA (pos,v'), List.map (subst subs) branches)
      | OO _ | TT _ -> APPLY (label, substlist branches))
  in subst1
