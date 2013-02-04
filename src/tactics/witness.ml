(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Helpers
open Names
open Variables
open Printer
open Printf
open Typesystem
open Lfcheck
open Wlfcheck
open Error

let first_var env =
  match env.tts_context with
  | (p,v,_) :: _ -> v
  | _ -> raise Internal

let first_w_var env =
  match env.tts_context with
  | (p,v,_) :: _ -> p
  | _ -> raise Internal

let abstract env x =
  nowhere 202 (LAMBDA(first_w_var env, nowhere 203 (LAMBDA(first_var env, x))))

let open_context t1 (env,o,t2) =
  let v = newfresh (Var "x") in
  let v' = newfresh (Var_wd "x") in
  let env = tts_bind env v' v t1 in
  let e = var_to_lf v' ** var_to_lf v ** END in 
  let o = Substitute.apply_args o e in
  let t2 = Substitute.apply_args t2 e in
  (env,o,t2)

let rec find_w_hastype env o t : tactic_return = (
  match unmark o with
  | APPLY(V v, END) -> (
      let (p,_) = tts_fetch v env in
      TacticSuccess (var_to_lf_pos (get_pos o) p)
     )
  | APPLY(O O_ev',args) -> (
      let (f,o,t1,t2) = args4 args in
      let tf = nowhere 1232 (APPLY(T T_Pi', t1 ** t2 ** END)) in
      match find_w_hastype env f tf with
      | TacticSuccess pf -> (
	  match find_w_hastype env o t1 with
	  | TacticSuccess po ->
	      let w = make_W_wev pf po in
	      TacticSuccess (nowhere 201 w)
	  | f -> f)
      | f -> f)
  | APPLY(O O_lambda',args) -> (
      let (t1',o) = args2 args in
      let (t1,t2) = unpack_Pi' t in
      let (env,o,t2) = open_context t1 (env,o,t2) in
      match find_w_hastype env o t2 with
      | TacticSuccess p ->
	  let w = make_W_wlam (abstract env p) in
	  let w = nowhere 204 w in
	  TacticSuccess w
      | f -> f)
  | _ -> 
      printf "%a: $witness failure\n%!" _pos (get_pos o);
      TacticFailure
 )

let witness (surr:surrounding) (env:context) (pos:position) (t:lf_type) (args:spine) : tactic_return = 
  match surr with 
  | (S_argument 1, None, Some j) :: _ -> (
      match unmark j with
      | F_Apply(F_witnessed_hastype,[_;o;t]) -> find_w_hastype env o t
      | _ -> TacticFailure)
  | (S_argument 1, Some t, None) :: (S_argument 1, None, Some j) :: _ -> (
      match unmark j with
      | F_Apply(F_istype,[_]) -> (
	  match unmark t with 
	  | APPLY(T T_El', ARG(o, _)) -> find_w_hastype env o uuu
	  | _ -> TacticFailure)
      | _ -> TacticFailure)
  | _ -> TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/witness.cmo "
  End:
 *)
