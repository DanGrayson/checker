(** Implement the binary equivalence algorithms from sections 5 and 6 of the paper as type checker for TS:

    [EEST]: Extensional Equivalence and Singleton Types
    by Christopher A. Stone and Robert Harper
    ACM Transactions on Computational Logic, Vol. 7, No. 4, October 2006, Pages 676-722.
*)

open Printf
open Printer
open Typesystem
open Lfcheck
open Error

exception Match_failure

let see n x = printf "\t  %s = %a\n%!" n _e x

let args2 s =
  match s with
  | ARG(x,ARG(y,END)) -> x,y
  | _ -> raise Match_failure

let rec head_reduction (env:context) (x:lf_expr) : lf_expr =
  raise NotImplemented

let rec head_normalization (env:context) (x:lf_expr) : lf_expr =
  raise NotImplemented

let rec term_equivalence (env:context) (x:lf_expr) (y:lf_expr) (t:lf_expr) : unit =
  raise NotImplemented

and path_equivalence (env:context) (x:lf_expr) (y:lf_expr) : lf_expr =
  raise NotImplemented

and type_equivalence (env:context) (t:lf_expr) (u:lf_expr) : unit =
  raise NotImplemented

and subtype (env:context) (t:lf_expr) (u:lf_expr) : unit =
  raise NotImplemented

let rec type_check (env:context) (e0:lf_expr) (t:lf_expr) : lf_expr option = (* returns a derivation of hastype e0 t, if possible *)
  (* assume t has been verified to be a type *)
  (* see figure 13, page 716 [EEST] *)
  match unmark e0, unmark t with
  | APPLY(O O_lambda, tx), APPLY(T T_Pi, tu) -> (
      let (t,x) = args2 tx in
      see "t" t; see "x" x;
      let (t',u) = args2 tu in
      see "t'" t'; see "u" u;
      raise Match_failure
      )
  | _ -> None

and type_synthesis (env:context) (m:lf_expr) : lf_expr =
  (* assume nothing *)
  (* see figure 13, page 716 [EEST] *)
  raise Match_failure

let type_validity (env:context) (t:lf_expr) =
  raise NotImplemented

let rec term_normalization (env:context) (x:lf_expr) (t:lf_expr) : lf_expr =
  raise NotImplemented

and path_normalization (env:context) (x:lf_expr) : lf_expr * lf_expr =
  raise NotImplemented

let rec type_normalization (env:context) (t:lf_expr) : lf_expr =
  raise NotImplemented

let tscheck surr env pos t args =
  match unmark t with
  | F_Apply(h,[x;t]) -> (
      printf "tscheck\n\t  x = %a\n\t  t = %a\n%!" _e x _e t;
      try 
	match type_check env x t 
	with
	| Some d -> TacticSuccess d
	| None -> TacticFailure
      with Match_failure -> TacticFailure)
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/tscheck.cmo "
  End:
 *)
