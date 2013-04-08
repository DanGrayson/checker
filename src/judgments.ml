(* -*- coding: utf-8 -*- *)

(** Judgments *)

include Expressions

type judgment_head =

  (* syntactic judgments *)
  | J_uexp | J_texp | J_oexp | J_wexp

  (* u-level comparison judgment, relative to current constraints *)
  | J_ulevel_equality

  (* expression comparison judgment, ignoring inessential subterms (written with ~) *)
  | J_type_uequality
  | J_object_uequality

  (* derivation tree judgments of TS *)
  | J_istype
  | J_hastype
  | J_type_equality
  | J_object_equality

  (* witnessed judgments of HTS *)
  | J_witnessed_istype
  | J_witnessed_hastype
  | J_witnessed_type_equality
  | J_witnessed_object_equality

type judgment = bare_judgment marked
and bare_judgment =
  | J_Basic of judgment_head * expr list
  | J_Pi of identifier * judgment * judgment
  | J_Singleton of (expr * judgment)
  | J_Sigma of identifier * judgment * judgment

type tts_judgment = 
  | TTS_istype
  | TTS_hastype of expr
  | TTS_type_equality of expr * expr
  | TTS_object_equality of expr * expr * expr                  (* (t, o, o') represents o = o' : t *)
  | TTS_template of string * tts_judgment * tts_judgment       (* x : J |- J'; with relative index 0 used to refer to x within J' *)

type tts_declaration = tts_judgment * expr option              (* a judgment with an optional definition (value) *)

(** Functions *)

let (@@) f x : judgment = nowhere 3 (J_Basic(f,x))

let istype t = J_istype @@ [t]				       (* t Type *)
let istype_v pos t = let t = id_to_expr pos t in istype t
let hastype o t = J_hastype @@ [o;t]			       (* o : t *)
let hastype_v t pos o = let o = id_to_expr pos o in hastype o t
let ulevel_equality u u' = J_ulevel_equality @@ [u;u']	       (* u ~ u' *)
let type_uequality t t' = J_type_uequality @@ [t;t']	       (* t ~ t' *)
let type_equality t t' = J_type_equality @@ [t;t']	       (* t = t' *)
let object_uequality o o' t = J_object_uequality @@ [o;o';t]   (* o ~ o' : t *)
let object_equality o o' t = J_object_equality @@ [o;o';t]     (* o = o' : t *)

let witnessed_istype t = J_witnessed_istype @@ [t]                                 (* t Type *)
let witnessed_istype_v pos t = 
  let t = id_to_expr pos t in witnessed_istype t
let witnessed_hastype t o = J_witnessed_hastype @@ [t;o]                           (* o : t *)
let witnessed_hastype_v t pos o = 
  let o = id_to_expr pos o in witnessed_hastype t o
let witnessed_type_equality t t' p = J_witnessed_type_equality @@ [t;t';p]         (* p : t = t' *)
let witnessed_type_equality_v t t' pos p = 
  let p = id_to_expr pos p in witnessed_type_equality t t' p
let witnessed_object_equality t o o' p = J_witnessed_object_equality @@ [t;o;o';p] (* p : o = o' : t *)
let witnessed_object_equality_v t o o' pos p = 
  let p = id_to_expr pos p in witnessed_object_equality t o o' p

(*
  Local Variables:
  compile-command: "make -C .. src/judgments.cmo "
  End:
 *)
