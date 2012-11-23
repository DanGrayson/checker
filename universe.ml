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
    | Upos (_,u) -> ev u
    | UEmptyHole -> raise Error.Internal
    | UNumberedEmptyHole n -> raise Error.Internal
    | Uvariable u -> index u
    | Uplus (x,n) -> ev x + n
    | Umax (x,y) -> max (ev x) (ev y)
    | U_def (d,u) -> raise Error.Internal in
  let chk lhs rhs = if (ev lhs) = (ev rhs) then raise Error.UniverseInconsistency in
  chk lhs rhs
    
let consistency uc = 
  let UContext (uv, eqns) = uc in 
  List.iter (chk uv) eqns

module Equal = struct
  let equiv uc = 			(* structural equality *)
    let rec ueq a b = a == b || ueq' (a,b)
    and ueq' = function
      | UEmptyHole, UEmptyHole -> true
      | UNumberedEmptyHole n, UNumberedEmptyHole n' -> n = n'
      | Uvariable Var x, Uvariable Var x' -> x = x'
      | Uplus (x,n), Uplus (x',n') -> ueq x x' && n = n'
      | Umax (x,y), Umax (x',y') -> ueq x x' && ueq y y'
      | U_def (d,u), U_def (d',u') -> raise Error.NotImplemented
      | _ -> false
    in ueq
end	  

module EquivA = struct
  let equiv uc lhs rhs = 		(* naive *)
    let UContext (uv, eqns) = uc in 
    try
      chk uv (lhs,rhs);
      true
    with
      Error.UniverseInconsistency -> false
end

module type Equivalence = sig
  val equiv : uContext -> uExpr -> uExpr -> bool
(*  val compare: uContext -> uExpr -> uExpr -> int *)
end
