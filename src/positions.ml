(** source file positions *)

type position =
  | Position of Lexing.position * Lexing.position (** start, end *)
  | Nowhere of int * int

type 'a marked = position * 'a
