(** A naive algorithm for checking consistency of a universe context.

    We set the i-th universe level variable to [100 * i], evaluate, and see
    whether the resulting equalities of natural numbers are true.  That amounts to
    taking the admissible set [A] in the paper to be the singleton set
    [A = {(0,100,200,...)}].

    We also implement the equivalence relation on universe levels given by 
    agreement on the set [A].

    Finally, we provide equality testing on universe levels, which is simply
    structural equality, not even normalized.

*)

open Typesystem

let rec memi' i x = function
    [] -> raise Error.Internal
  | a::l -> if a = x then i else memi' (i+1) x l

let memi x = memi' 0 x

let chk uv (lhs,rhs) =
  let index name = memi name uv in
  let rec ev = function
    | POS(_,e) -> (match e with
	| Variable u -> index u
	| APPLY(U U_next,[u]) -> (ev u) + 1
	| APPLY(U U_max,[u;v]) -> max (ev u) (ev v)
	| _ -> raise Error.Internal)
    | _ -> raise Error.Internal
  in let chk lhs rhs = if (ev lhs) = (ev rhs) then raise Error.UniverseInconsistency in
  chk lhs rhs
    
let consistency ulevel_context = 
  let UContext (uv, eqns) = ulevel_context in 
  List.iter (chk uv) eqns

module Equal = struct
  let equiv ulevel_context = 			(* structural equality *)
    let rec ueq a b = match (a,b) with
    | POS(_,a), POS(_,b) -> (
	a == b || 
	match (a,b) with 
	| Variable x, Variable x' -> x = x'
	| APPLY(U U_next, [x ]),
	  APPLY(U U_next, [x']) -> ueq x x'
	| APPLY(U U_max, [x;y]), 
	  APPLY(U U_max, [x';y']) -> ueq x x' && ueq y y'
	| _ -> false)
    | _ -> false
    in ueq
end

module EquivA = struct
  let equiv ulevel_context lhs rhs = 		(* naive *)
    let UContext (uv, eqns) = ulevel_context in 
    try
      chk uv (lhs,rhs);
      true
    with
      Error.UniverseInconsistency -> false
end

module type Equivalence = sig
  val equiv : uContext -> expr -> expr -> bool
(*  val compare: uContext -> expr -> expr -> int *)
end
