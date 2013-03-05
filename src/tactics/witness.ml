(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Helpers
open Names
open Variables
open Printer
open Printf
open Typesystem
open Lfcheck
open Error

exception WitnessNotFound

let abstract env x =
  nowhere 202 (LAMBDA(first_var env, nowhere 203 (LAMBDA(first_w_var env, x))))

let open_context t1 (env,o,t2) =
  let env = local_tts_bind env "x" t1 in
  let e = var_to_lf (VarRel 1) ** var_to_lf (VarRel 0) ** END in
  let o = Substitute.apply_args 1 o e in
  let t2 = Substitute.apply_args 1 t2 e in
  (env,o,t2)

let rec this_head_reduces env o =   (* returns (p,o'), where p : o == o' : _ *)
  (* raises Not_found if there is no head reduction *)
  try
    let f,o1,t1',t2 = unpack_ev' o in
    let t1,o2 = unpack_lambda' f in
    let p1 = find_w_hastype env o1 t1 in
    let env,o2',t2' = open_context t1 (env,o2,t2) in
    let p2 = find_w_hastype env o2' t2' in
    let o' = apply_2 1 o2 o1 p1 in
    let p = make_W_wbeta p1 (abstract env p2) in
    nowhere 207 p, o'
  with
    FalseWitness -> raise Not_found

and find_w_hastype env o t : lf_expr = (
  match unmark o with
  | APPLY(V (VarRel i), END) ->
      assert (i mod 2 = 0);
      var_to_lf_pos (get_pos o) (VarRel (i+1))	(*??*)
  | APPLY(O O_ev',args) ->
      let (f,o,t1,t2) = args4 args in
      let tf = nowhere 206 (make_T_Pi' t1 t2) in
      let pf = find_w_hastype env f tf in
      let po = find_w_hastype env o t1 in
      let w = make_W_wev pf po in
      nowhere 201 w
  | APPLY(O O_lambda',args) ->
      let (t1',o) = args2 args in
      let (t1,t2) = unpack_Pi' t in
      let (env,o,t2) = open_context t1 (env,o,t2) in
      let p = find_w_hastype env o t2 in
      let w = make_W_wlam (abstract env p) in
      nowhere 204 w
  | _ ->
      printf "%a: $witness failure\n%!" _pos (get_pos o);
      raise WitnessNotFound
 )

let rec find_w_type_equality env t t' =
  if term_equiv t t' then (
    nowhere 206 make_W_Wrefl)
  else (
    match unmark t, unmark t' with
    | APPLY(T T_El', args), APPLY(T T_El', args') -> (
	let o,p = args2 args in
	let o',p' = args2 args' in
	let peq = find_w_object_equality env o o' uuu in
	let w = make_W_weleq peq in
	nowhere 208 w)
    | _ -> raise WitnessNotFound)

and find_w_object_equality env o o' t =
  if term_equiv o o' then (
    let p = find_w_hastype env o t in
    let p' = find_w_hastype env o' t in
    let w = make_W_wrefl p p' in
    nowhere 205 w)
  else (
    try
      let (q,oo) = this_head_reduces env o in
      if term_equiv oo o' then q
      else raise WitnessNotFound
    with Not_found -> (
      let (q,oo') = this_head_reduces env o' in
      if term_equiv o oo' then raise NotImplemented
      else raise WitnessNotFound
      )
   )

let witness (surr:surrounding) (env:environment) (pos:position) (t:lf_type) (args:spine) : tactic_return =
  try
    match surr with
    | (S_argument 1, None, Some (pos,F_Apply(F_witnessed_hastype,[_;o;t]))) :: _ ->
	TacticSuccess (find_w_hastype env o t)
    | (S_argument 1, None, Some (pos,F_Apply(F_witnessed_object_equality,[_;o;o';t]))) :: _ ->
	TacticSuccess (find_w_object_equality env o o' t)
    | (S_argument 1, None, Some (pos,F_Apply(F_witnessed_type_equality,[_;t;t']))) :: _ ->
	TacticSuccess (find_w_type_equality env t t')
    | (S_argument 1, Some (pos,APPLY(T T_El', ARG(o, _))), None) :: _ ->
	TacticSuccess (find_w_hastype env o uuu)
    | _ -> TacticFailure
  with
    WitnessNotFound -> TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/witness.cmo "
  End:
 *)
