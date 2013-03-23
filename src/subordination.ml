(** Subordination *)

(** see section 2.4 of Mechanizing Meta-theory by Harper and Licata *)

open Kinds

type kind_comparison = K_less_equal | K_greater | K_incomparable

let rec ultimate_kind = function
  | K_ulevel
  | K_syntactic_judgment
  | K_derived_judgment
  | K_witnessed_judgment
  | K_basic_judgment as k -> k
  | K_Pi (v,t,k) -> ultimate_kind k

let rec compare_kinds k l =
  let k = ultimate_kind k in
  let l = ultimate_kind l in
  if k = l then K_less_equal else
  let le = function
    | K_ulevel, _
    | K_syntactic_judgment, (K_basic_judgment|K_derived_judgment|K_witnessed_judgment) 
    | K_basic_judgment, (K_derived_judgment|K_witnessed_judgment)
      -> true
    | _ 
      -> false in
  if le(k,l) then K_less_equal
  else if le(l,k) then K_greater
  else K_incomparable

(*
  Local Variables:
  compile-command: "make -C .. src/subordination.cmo "
  End:
 *)
