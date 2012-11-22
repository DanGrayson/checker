(** Exceptions, error message handling, and source code positions. *)

exception UniverseInconsistency
exception GeneralError of string
exception GensymCounterOverflow
exception NotImplemented
exception Unimplemented of string
exception Internal
exception VariableNotInContext
exception NoMatchingRule
exception Eof

type position =
  | Position of Lexing.position * Lexing.position (** start, end *)
  | Nowhere

exception TypingError of position * string
exception TypingUnimplemented of position * string
exception TypeCheckingFailure of position * string
exception TypeCheckingFailure2 of position * string * position * string
exception TypeCheckingFailure3 of position * string * position * string * position * string

let error_format_pos = function
  | Position(p,q) 
    -> "File \"" ^ p.Lexing.pos_fname ^ "\", " 
      ^ (if p.Lexing.pos_lnum = q.Lexing.pos_lnum
	 then "line " ^ (string_of_int p.Lexing.pos_lnum) 
	 else "lines " ^ (string_of_int p.Lexing.pos_lnum) ^ "-" ^ (string_of_int q.Lexing.pos_lnum))
      ^ ", " 
      ^ (let i = p.Lexing.pos_cnum-p.Lexing.pos_bol+1
         and j = q.Lexing.pos_cnum-q.Lexing.pos_bol in
         if i = j
	 then "character " ^ (string_of_int i)
         else "characters " ^ (string_of_int i) ^ "-" ^ (string_of_int j))
  | Nowhere -> "nowhere:0:0"

let nopos x = error_format_pos Nowhere
