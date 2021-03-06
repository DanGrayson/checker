(** Structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Typesystem

module type S =
  sig
    val uequiv     : uContext -> expr -> expr -> bool
    val term_equiv : uContext -> int -> expr -> expr -> bool
    val type_equiv : uContext -> int -> judgment -> judgment -> bool
  end

module UEqual : S
module UEquivA : S
