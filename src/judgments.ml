(* -*- coding: utf-8 -*- *)

include Expressions

type judgment_head =
  (* syntactic judgments: *)
  | J_uexp | J_texp | J_oexp | J_wexp
  (* witnessed judgments of TTS: *)
  | J_istype_witnessed_inside
  | J_witnessed_hastype
  | J_witnessed_type_equality
  | J_witnessed_object_equality
  (* derivation tree judgments of TS: *)
  | J_istype
  | J_hastype
  | J_type_equality
  | J_object_equality
  (* u-level comparison judgment, relative to current constraints *)
  | J_ulevel_equality
  (* expression comparison judgment, ignoring inessential subterms, written with ~ *)
  | J_type_uequality
  | J_object_uequality

type judgment = bare_judgment marked
and bare_judgment =
  | J_Basic of judgment_head * expr list
  | J_Pi of identifier * judgment * judgment
  | J_Singleton of (expr * judgment)
  | J_Sigma of identifier * judgment * judgment

(*
  Local Variables:
  compile-command: "make -C .. src/judgments.cmo "
  End:
 *)
