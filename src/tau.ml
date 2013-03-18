open Printf
open Printer
open Error
open Typesystem
open Names
open Helpers

let rec tau (env:environment) e : expr =
  let pos = get_pos e in
  match unmark e with
  | BASIC(V (Var v),FST END) -> (		(* pi1 v *)
      if !debug_mode then printf " v = %a\n%!" _i v;
      if !debug_mode then print_context (Some 4) stderr env;
      let t =
	try List.assoc v env.local_lf_context
	with Not_found -> raise (TypeCheckingFailure(env, [], [pos, "variable not in LF context: " ^ idtostring v])) in
      match unmark t with
      | J_Sigma(_,_,(_,J_Basic(J_hastype,[(_,BASIC(V v',END)); t]))) -> t
      | _ -> (trap(); raise Internal))
  | BASIC(h,args) -> (
      match h with
      | TACTIC _ -> raise NotImplemented
      | V v ->
          let t =
            try ts_fetch env v
            with Not_found -> raise (TypeCheckingFailure(env, [], [pos, "variable not in TS context: " ^ vartostring v]))
          in
          (
           match args with
           | END -> t
           | _ -> raise NotImplemented
          )
      | W wh -> raise (TypeCheckingFailure(env, [],[pos, "a w-expression doesn't have a type"]))
      | U uh -> raise (TypeCheckingFailure(env, [],[pos, "a u-expression doesn't have a type"]))
      | T th -> raise (TypeCheckingFailure(env, [], [pos, "a t-expression doesn't have a type"]))
      | O oh -> with_pos pos (
          match oh with
          | O_u -> (
              match args with
              | ARG(u,END) -> make_T_U (pos, (make_U_next u))
              | _ -> raise (TypeCheckingFailure(env, [], [pos, "expected [u] to have one branch"])))
          | O_j -> (
              match args with
              | ARG(m1,ARG(m2,END)) ->
                  make_T_Pi
                    (with_pos_of m1 (make_T_U m1))
                    (id "_", (with_pos_of m2 (make_T_U m2)))
              | _ -> raise (TypeCheckingFailure(env, [], [pos, "expected [j] to have two branches"])))
          | O_ev' -> (
              match args with
              | ARG(f,ARG(o,ARG(t1,ARG((_,TEMPLATE(x,(pos,TEMPLATE(w,t2)))),END)))) ->
		  let t2 = Substitute.subst_expr o t2 in
		  let t2 = Substitute.subst_expr (pos,default_tactic (* ? *)) t2 in
                  unmark t2
              | _ -> raise Internal)
          | O_ev -> (
              match args with
              | ARG(f,ARG(o,ARG(t1,ARG((_,TEMPLATE(x,t2)),END)))) ->
                  unmark (Substitute.subst_expr o t2)
              | _ -> raise Internal)
          | O_lambda' -> (
              match args with
              | ARG(t,ARG(o,END)) ->
		  let x = id "x" in
		  let x' = id_to_expr_bare x in
		  let w = idw "x" in
		  let w' = id_to_expr_bare w in
                  make_T_Pi' t (lambda2 x w (tau (ts_bind env x t) (Substitute.apply_args o (ARG(x',ARG(w',END))))))
              | _ -> raise Internal)
          | O_lambda -> (
              match args with
              | ARG(t,ARG(o,END)) ->
		  let x = id "x" in
		  let x' = id_to_expr_bare x in
                  make_T_Pi t (x, tau (ts_bind env x t) (Substitute.apply_args o (ARG(x',END))))
              | _ -> raise Internal)
          | O_forall -> (
              match args with
              | ARG(u,ARG(u',_)) ->
                  make_T_U (nowhere 6 (make_U_max u u'))
              | _ -> raise Internal)
          | O_tt -> make_T_Pt
          | O_pair | O_pr1 | O_pr2 | O_total | O_pt | O_pt_r | O_coprod | O_ii1
          | O_ii2 | O_sum | O_empty | O_empty_r | O_c | O_ip_r | O_ip
          | O_paths | O_refl | O_J | O_rr0 | O_rr1
	  | O_nat | O_nat_r | O_O | O_S
            -> raise NotImplemented
         ) )
  | _ -> raise (TypeCheckingFailure(env, [], [pos, "a canonical LF expression has no TS type"]))

(*
  Local Variables:
  compile-command: "make -C .. src/tau.cmo "
  End:
 *)
