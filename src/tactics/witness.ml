(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Error
open Helpers
open Names
open Printer
open Printf
open Typesystem
open Lfcheck

exception WitnessNotFound

let abstract env x =
  nowhere 202 (TEMPLATE(first_var env, nowhere 203 (TEMPLATE(first_w_var env, x))))

let open_context t1 (env,o,t2) =
  let env = local_tts_declare_object env "x" t1 in
  let e = var_to_expr_bare (Rel 1) ** var_to_expr_bare (Rel 0) ** END in
  let o = Substitute.apply_args (rel_shift_expr 1 o) e in
  let t2 = Substitute.apply_args (rel_shift_expr 1 t2) e in
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

and find_w_hastype env o t : expr = (
  if tactic_tracing then printf "tactic: find_w_hastype: t=%a; o=%a\n%!" _e (env,t) _e (env,o);
  let r = 
  match unmark o with
  | BASIC(V v, END) ->
      let t' = tts_fetch_type env v in
      if term_equiv t t'
      then var_to_expr (get_pos o) (witness_var v)
      else raise WitnessNotFound
  | BASIC(O O_ev',args) ->
      let (f,o,t1,t2) = args4 args in
      let tf = nowhere 206 (make_T_Pi' t1 t2) in
      let pf = find_w_hastype env f tf in
      let po = find_w_hastype env o t1 in
      let w = make_W_wev pf po in
      nowhere 201 w
  | BASIC(O O_lambda',args) ->
      let (t1',o) = args2 args in
      let (t1,t2) = unpack_Pi' t in
      let (env,o,t2) = open_context t1 (env,o,t2) in
      let p = find_w_hastype env o t2 in
      let w = make_W_wlam (abstract env p) in
      nowhere 204 w
  | _ ->
      printf "%a: $witness failure\n%!" _pos (get_pos o);
      raise WitnessNotFound
  in
  if tactic_tracing then printf "tactic: find_w_hastype: returning %a\n%!" _e (env,r);
  r
 )

let rec find_w_type_equality env t t' =
  if term_equiv t t' then (
    nowhere 206 make_W_Wrefl)
  else (
    match unmark t, unmark t' with
    | BASIC(T T_El', args), BASIC(T T_El', args') -> (
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

let witness (surr:surrounding) (env:environment) (pos:position) (t:judgment) (args:expr_list) : tactic_return =
  try
    match surr with
    | (env,S_type_family_args(3,[o;t]), None, Some (_,J_Basic(J_witnessed_hastype,_))) :: _ ->
	TacticSuccess (find_w_hastype env o t)
    | (env,S_type_family_args(4,[o';o;t]), None, Some (_,J_Basic(J_witnessed_object_equality,_))) :: _ ->
	TacticSuccess (find_w_object_equality env o o' t)
    | (env,S_type_family_args(3,[t';t]), None, Some (pos,J_Basic(J_witnessed_type_equality,_))) :: _ ->
	TacticSuccess (find_w_type_equality env t t')
    | (env,S_expr_list'(1,T T_El',ARG(o,_),_), _, _) :: _ -> TacticSuccess (find_w_hastype env o uuu)
    | _ -> 
	printf "witness: unfamiliar surrounding\n%!";
	print_surroundings surr;
	TacticFailure
  with
    WitnessNotFound -> TacticFailure

(*
  Local Variables:
  compile-command: "make -C ../.. src/tactics/witness.cmo "
  End:
 *)
