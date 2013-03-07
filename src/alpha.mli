(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Variables
open Typesystem

module type S =
  sig
    val uequiv     : uContext -> lf_expr -> lf_expr -> bool
    val term_equiv : uContext -> int -> lf_expr -> lf_expr -> bool
    val type_equiv : uContext -> int -> lf_type -> lf_type -> bool
  end

module UEqual : S
module UEquivA : S
