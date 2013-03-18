(** Subordination: see section 2.4 of Mechanizing Meta-theory by Harper and Licata *)

open Kinds

type kind_comparison = K_equal | K_less | K_greater | K_incomparable

let rec ultimate_kind = function
  | K_ulevel
  | K_term
  | K_derivation_tree_judgment
  | K_witnessed_judgment
  | K_primitive_judgment as k -> k
  | K_Pi (v,t,k) -> ultimate_kind k

let rec compare_kinds k l =
  let k = ultimate_kind k in
  let l = ultimate_kind l in
  if k = l then K_equal else
  match k,l with
  | K_primitive_judgment, K_derivation_tree_judgment
  | K_derivation_tree_judgment,           K_primitive_judgment
      -> K_equal
  | K_ulevel,             _
  | K_term,         K_derivation_tree_judgment
  | K_term,         K_primitive_judgment
  | K_term,         K_witnessed_judgment
  | K_primitive_judgment, K_witnessed_judgment
    -> K_less
  | _,                    K_ulevel
  | K_derivation_tree_judgment,           K_term
  | K_primitive_judgment, K_term
  | K_witnessed_judgment, K_term
  | K_witnessed_judgment, K_primitive_judgment
    -> K_greater
  | _ -> K_incomparable

(*
  Local Variables:
  compile-command: "make -C .. src/subordination.cmo "
  End:
 *)
