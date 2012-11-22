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
let rec substlist subs es = List.map (subst subs) es
and subst subs = function
  | LAMBDA((pos,v), bodies) -> 
      let w = newfresh v in
      let v' = POS(pos, OO_variable w) in
      let subs = (v,v') :: subs in 
      LAMBDA((pos,w), List.map (subst subs) bodies)
  | POS(pos,e) as d -> match e with 
    | APPLY(label,args) -> POS(pos, APPLY(label,substlist subs args))
    | OO_variable v -> (try List.assoc v subs with Not_found -> d)
    | UU _ | TT_variable _ -> d
  

