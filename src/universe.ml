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
open Printf
open Printer

exception Inconsistency of lf_expr * lf_expr

let rec memi' i x = function
    [] -> (trap(); raise Internal)
  | a::l -> if a = x then i else memi' (i+1) x l

let memi x = memi' 0 x

let step_size = 10

let chk uv ((lhs:lf_expr),(rhs:lf_expr)) =
  let index name = memi name uv in
  let rec ev e =
    let (pos,e0) = e
    in match e0 with
    | APPLY(V u,END) -> 
	if true then printf " Universe.chk: u=%a uv=%a\n%!" _v u _vl uv;
	- step_size * (index u)
    | APPLY(U U_next,ARG(u,END)) -> (ev u) + 1
    | APPLY(U U_max,ARG(u,ARG(v,END))) -> max (ev u) (ev v)
    | _ -> (
	printf "%a: unexpected u-expression: %a\n%!" _pos pos _e e;
	trap(); raise Internal)
  in
  if (ev lhs) != (ev rhs) then raise (Inconsistency (lhs, rhs))

let get_uvars env =
  printf "get_uvars:\n"; print_context (Some 20) stdout env;
  let rec get_uvars accu = function
  | [] -> List.rev accu
  | (u,t) :: rest -> if t = uexp then get_uvars (u :: accu) rest else get_uvars accu rest
  in get_uvars [] env.lf_context

let get_ueqns env =
  let rec get_ueqns accu = function
  | (_, (pos,F_Apply(F_ulevel_equality,[u; u']))) :: rest -> get_ueqns ((u,u') :: accu) rest
  | _ :: rest -> get_ueqns accu rest
  | [] -> List.rev accu
  in get_ueqns [] env.lf_context

let chk_var_ueqns uv eqns = List.iter (chk uv) eqns

let consistency env =
  List.iter (chk (get_uvars env)) (get_ueqns env)

let chk_ueqns env ueqns = chk_var_ueqns (get_uvars env) ueqns

module Equal = struct
  let term_equiv ulevel_context = 			(* structural equality *)
    let rec ueq a b =
      unmark a == unmark b ||
      match (unmark a,unmark b) with
      | APPLY(V x,END), APPLY(V x',END) -> x = x'
      | APPLY(U U_next, ARG(x ,END)), APPLY(U U_next, ARG(x',END)) -> ueq x x'
      | APPLY(U U_max, ARG(x,ARG(y,END))), APPLY(U U_max, ARG(x',ARG(y',END))) -> ueq x x' && ueq y y'
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

(*
  Local Variables:
  compile-command: "make -C .. src/universe.cmo "
  End:
 *)
