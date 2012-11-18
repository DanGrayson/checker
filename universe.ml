(** Here we implement a naive algorithm for checking consistency of a universe context.

    We set the i-th universe level variable to [100 * i], evaluate, and see
    whether the resulting equalities of natural numbers are true.
*)

open Typesystem

let rec memi' i x = function
    [] -> raise InternalError
  | a::l -> if a = x then i else memi' (i+1) x l

let memi x = memi' 0 x

exception UniverseInconsistency

let consistency uc = (
  let UContext (uv, eqns) = uc in 
  let index name = memi name uv in
  let rec ev u = ev' (strip_pos u)
  and ev' = function
    | UEmptyHole -> raise InternalError
    | UNumberedEmptyHole n -> raise InternalError
    | Uvariable u -> index u
    | Uplus (x,n) -> ev x + n
    | Umax (x,y) -> max (ev x) (ev y)
    | U_def (d,u) -> raise InternalError in
  let chk (lhs,rhs) = if (ev lhs) = (ev rhs) then raise UniverseInconsistency in
  List.iter chk eqns
)

