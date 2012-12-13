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

open Error
open Variables
open Typesystem

exception Inconsistency of lf_expr * lf_expr

let rec memi' i x = function
    [] -> raise Error.Internal
  | a::l -> if a = x then i else memi' (i+1) x l

let memi x = memi' 0 x

let step_size = 10

let chk uv ((lhs:lf_expr),(rhs:lf_expr)) =
  let index name = memi name uv in
  let rec ev e = 
    let (pos,e0) = e 
    in match e0 with
    | EVAL(V u,END) -> - step_size * (index u)
    | EVAL(U U_next,ARG(u,END)) -> (ev u) + 1
    | EVAL(U U_max,ARG(u,ARG(v,END))) -> max (ev u) (ev v)
    | _ -> raise Error.Internal
  in 
  if (ev lhs) != (ev rhs) then raise (Inconsistency (lhs, rhs))

let get_uvars =
  let rec get_uvars accu = function
  | [] -> List.rev accu
  | (u,t) :: rest -> if t = uexp then get_uvars (u :: accu) rest else get_uvars accu rest
  in get_uvars []

let get_ueqns =
  let rec get_ueqns accu = function
  | (_, (pos,F_APPLY(F_ulevel_equality,[u; u']))) :: rest -> get_ueqns ((u,u') :: accu) rest
  | _ :: rest -> get_ueqns accu rest 
  | [] -> List.rev accu
  in get_ueqns []

let chk_var_ueqns uv eqns = List.iter (chk uv) eqns

let consistency env  = List.iter (chk (get_uvars env)) (get_ueqns env)

let chk_ueqns env ueqns = chk_var_ueqns (get_uvars env) ueqns

let ubind env uvars ueqns =
  let env = List.rev_append (List.map (fun u -> ((Var u), uexp)) uvars) env in
  let env = List.rev_append (List.map (fun (u,v) -> (Variables.newfresh (Var "ueq"), ulevel_equality u v)) ueqns) env in
  chk_ueqns env ueqns;
  env

module Equal = struct
  let term_equiv ulevel_context = 			(* structural equality *)
    let rec ueq a b = 
      let (a,b) = (unmark a,unmark b) in
      a == b || 
      match (a,b) with 
      | EVAL(V x,END), EVAL(V x',END) -> x = x'
      | EVAL(U U_next, ARG(x ,END)), EVAL(U U_next, ARG(x',END)) -> ueq x x'
      | EVAL(U U_max, ARG(x,ARG(y,END))), EVAL(U U_max, ARG(x',ARG(y',END))) -> ueq x x' && ueq y y'
      | _ -> false
    in ueq
end

module EquivA = struct
  let term_equiv ulevel_context lhs rhs = 		(* naive *)
    try
      (* not implemented *)
      true
    with
      Inconsistency _ -> false
end

module type Equivalence = sig
  val term_equiv : uContext -> lf_expr -> lf_expr -> bool
end
