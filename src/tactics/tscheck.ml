(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper as type checker for TS:

    [EEST]: Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676-722.

*)

open Variables
open Printf
open Printer
open Typesystem
open Lfcheck
open Error
open Helpers

let see n x = printf "\t  %s = %a\n%!" n _e x

(** returns a term y and a derivation of hastype y t and a derivation of oequal x y t *)
let rec head_reduction (env:environment) (t:lf_expr) (dt:lf_expr) (x:lf_expr) (dx:lf_expr) : lf_expr * lf_expr * lf_expr =
  (* dt : istype t *)
  (* dx : hastype x t *)
  raise NotImplemented

(** returns a term y and a derivation of hastype y t and a derivation of oequal x y t *)
let rec head_normalization (env:environment) (t:lf_expr) (dt:lf_expr) (x:lf_expr) (dx:lf_expr) : lf_expr * lf_expr * lf_expr =
  (* dt : istype t *)
  (* dx : hastype x t *)
  raise NotImplemented

(** returns a derivation of oequal x y t *)
let rec term_equivalence (env:environment) (x:lf_expr) (dx:lf_expr) (y:lf_expr) (dy:lf_expr) (t:lf_expr) (dt:lf_expr) : lf_expr =
  (* dt : istype t *)
  (* dx : hastype x t *)
  (* dy : hastype y t *)
  raise NotImplemented

(** returns a type t and derivation of hastype x t, hastype y t, oequal x y t *)
and path_equivalence (env:environment) (x:lf_expr) (y:lf_expr) : lf_expr * lf_expr * lf_expr =
  raise NotImplemented

(** returns a derivation of tequal t u *)
and type_equivalence (env:environment) (t:lf_expr) (dt:lf_expr) (u:lf_expr) (du:lf_expr) : lf_expr =
  (* dt : istype t *)
  (* du : istype u *)
  raise NotImplemented

(** returns a derivation of hastype e t *)
let rec type_check (env:environment) (e:lf_expr) (t:lf_expr) (dt:lf_expr) : lf_expr =
  (* dt : istype t *)
  (* see figure 13, page 716 [EEST] *)
  let (s,ds,h) = type_synthesis env e in	(* ds : istype x ; h : hastype e s *)
  if Alpha.UEqual.term_equiv empty_uContext s t then h
  else 
  let e = type_equivalence env s ds t dt in	(* e : tequal s t *)
  ignore e;
  raise NotImplemented			(* here we'll apply the rule "cast" *)

(** returns a type t and derivations of istype t and hastype x t *)
and type_synthesis (env:environment) (x:lf_expr) : lf_expr * lf_expr * lf_expr =
  (* assume nothing *)
  (* see figure 13, page 716 [EEST] *)

  (* match unmark e with *)
  (* | APPLY(O O_lambda, tx) -> ( *)
  (*     let (t,x) = args2 tx in *)

  raise NotImplemented

(** returns a derivation of istype t *)
let type_validity (env:environment) (t:lf_expr) : lf_expr =
  raise NotImplemented

(** returns a term y and a derivation of hastype y t and a derivation of oequal x y t *)
let rec term_normalization (env:environment) (t:lf_expr) (dt:lf_expr) (x:lf_expr) (dx:lf_expr) : lf_expr * lf_expr * lf_expr =
  (* dt : istype t *)
  (* dx : hastype x t *)
  raise NotImplemented

(** returns the type t of x and derivations of istype t and hastype x t  *)
and path_normalization (env:environment) (x:lf_expr) : lf_expr * lf_expr * lf_expr =
  raise NotImplemented

let rec type_normalization (env:environment) (t:lf_expr) : lf_expr =
  raise NotImplemented

let self = nowhere 1234 (cite_tactic (Tactic_name "tscheck") END)

let rec tscheck surr env pos tp args =
  if tactic_tracing then printf "tscheck: tp = %a\n%!" _t tp;
  match unmark tp with
  | F_Apply(F_istype,[t]) -> (
      if tactic_tracing then see "t" t;
      match unmark t with 
      | APPLY(T T_Pi,args) -> (
	  let (a,b) = args2 args in
	  if tactic_tracing then (see "a" a; see "b" b);
	  TacticSuccess ( with_pos_of t (APPLY(V (Var "∏_istype"), a ** b ** CDR(self ** self ** END))) )
	 )
      | _ -> Default.default surr env pos tp args
      )
  | F_Apply(F_hastype,[x;t]) -> (
      if tactic_tracing then printf "tscheck\n\t  x = %a\n\t  t = %a\n%!" _e x _e t;
      try
	let dt = type_validity env t in	(* we should be able to get this from the context *)
	TacticSuccess (type_check env x t dt)
      with
	NotImplemented|Args_match_failure -> TacticFailure
     )
  | F_Pi(v,a,b) -> (
      match tscheck surr (lf_bind env v a) (get_pos tp) b args with 
      | TacticSuccess e -> TacticSuccess (with_pos pos (LAMBDA(v,e)))
      | TacticFailure as r -> r)
  | _ -> Default.default surr env pos tp args

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/tscheck.cmo "
  End:
 *)
