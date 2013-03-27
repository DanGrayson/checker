(** This tactic attempts to fill an empty hole of type [wexp] with an appropriate witness to the proof. *)

open Error
open Helpers
open Names
open Printer
open Printf
open Typesystem
open Lfcheck

exception WitnessNotFound

let abstract env x = nowhere 202 (TEMPLATE(first_var env, x))

let open_context t1 (env,o,t2) =
  let env = local_tts_declare_object env "x" t1 in
  let e = var_to_expr_bare (Rel 1) ** var_to_expr_bare (Rel 0) ** END in
  let o = Substitute.apply_args (rel_shift_expr 1 o) e in
  let t2 = Substitute.apply_args (rel_shift_expr 1 t2) e in
  (env,o,t2)

let rec this_head_reduces env o =   (* returns (p,o'), where p : o == o' : _ *)
  (* raises Not_found if there is no head reduction *)
  try
    let f,o1,t1',t2 = unpack_ev o in
    let t1,o2 = unpack_lambda f in
    let o' = apply_1 1 o2 o1 in
    let p = make_W_wbeta in
    nowhere 207 p, o'
  with
    FalseWitness -> raise Not_found

let rec find_w_type_equality env t t' =
  if term_equiv t t' then (
    nowhere 206 make_W_Wrefl)
  else (
    match unmark t, unmark t' with
    | BASIC(T T_El, args), BASIC(T T_El, args') -> (
	let o = args1 args in
	let o' = args1 args' in
	let peq = find_w_object_equality env o o' uuu in
	let w = make_W_weleq peq in
	nowhere 208 w)
    | _ -> raise WitnessNotFound)

and find_w_object_equality env o o' t =
  if term_equiv o o' then (
    let w = make_W_wrefl in
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
	TacticSuccess (raise NotImplemented)
    | (env,S_type_family_args(4,[o';o;t]), None, Some (_,J_Basic(J_witnessed_object_equality,_))) :: _ ->
	TacticSuccess (find_w_object_equality env o o' t)
    | (env,S_type_family_args(3,[t';t]), None, Some (pos,J_Basic(J_witnessed_type_equality,_))) :: _ ->
	TacticSuccess (find_w_type_equality env t t')
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
