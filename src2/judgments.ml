(* -*- coding: utf-8 -*- *)

(** Judgments *)

include Expressions

type judgment = 
  | J_context_okay			           (* represents |- okay *)
  | J_istype of expr			           (* t represents |- t type *)
  | J_hastype of expr * expr		           (* (t,o) represents |- o : t *)
  | J_type_equality of expr * expr * expr	   (* (t,t',p) represents |- p : t = t' *)
  | J_object_equality of expr * expr * expr * expr (* (t, o, o',p) represents |- p : o = o' : t *)

(** Functions *)

(*
  Local Variables:
  compile-command: "make -C .. src/judgments.cmo "
  End:
 *)
