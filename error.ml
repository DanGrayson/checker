(** Exceptions, error message handling, and source code positions. *)

(** Source code positions. *)

let debug_mode = ref false

let trap () = ()

type position =
  | Position of Lexing.position * Lexing.position (** start, end *)
  | Nowhere of int * int

let lexbuf_position lexbuf =
    Position ( Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf )

let errfmt = function
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
  | Nowhere(i,j) -> "nowhere:"^(string_of_int i)^":"^(string_of_int j)

type 'a marked = position * 'a
let unmark ((_:position), x) = x
let get_pos ((pos:position), _) = pos
let errpos x = errfmt (get_pos x)
let with_pos (pos:position) e = (pos, e)
let with_pos_of ((pos:position),_) e = (pos,e)
let nowhere_ctr = ref 0
let no_pos i = incr nowhere_ctr; Nowhere(i, !nowhere_ctr)
let nowhere i x = (no_pos i,x)
let nopos i = errfmt (no_pos i)
let seepos pos = Printf.fprintf stderr "%s: ... debugging ...\n" (errfmt pos); flush stderr

exception DebugMe
exception GeneralError of string
exception GensymCounterOverflow
exception NotImplemented
exception Unimplemented of string
exception Internal
exception VariableNotInContext
exception NoMatchingRule
exception Eof
exception MarkedError of position * string
