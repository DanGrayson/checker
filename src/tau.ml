open Printf
open Printer
open Error
open Variables
open Typesystem
open Names

let rec tau (env:environment) e : lf_expr =
  let pos = get_pos e in
  match unmark e with
  | APPLY(V v,CAR END) -> (		(* pi1 v *)
      if !debug_mode then printf " v = %a\n%!" _v v;
      if !debug_mode then print_context (Some 4) stderr env;
      let t =
	try List.assoc v env.local_lf_context
	with Not_found -> raise (TypeCheckingFailure(env, [], [pos, "variable not in LF context: " ^ vartostring v])) in
      match unmark t with
      | F_Sigma(_,_,(_,F_Apply(F_hastype,[(_,APPLY(V v',END)); t]))) -> t
      | _ -> (trap(); raise Internal))
  | APPLY(h,args) -> (
      match h with
      | TAC _ -> raise NotImplemented
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
              | ARG(u,END) -> Helpers.make_T_U (pos, (Helpers.make_U_next u))
              | _ -> raise (TypeCheckingFailure(env, [], [pos, "expected [u] to have one branch"])))
          | O_j -> (
              match args with
              | ARG(m1,ARG(m2,END)) ->
                  Helpers.make_T_Pi
                    (with_pos_of m1 (Helpers.make_T_U m1))
                    (Var "_", (with_pos_of m2 (Helpers.make_T_U m2)))
              | _ -> raise (TypeCheckingFailure(env, [], [pos, "expected [j] to have two branches"])))
          | O_ev' -> raise NotImplemented
          | O_ev -> (
              match args with
              | ARG(f,ARG(o,ARG(t1,ARG((_,LAMBDA(x,t2)),END)))) ->
                  unmark (Substitute.subst_expr o t2)
              | _ -> raise Internal)
          | O_lambda' -> raise NotImplemented
          | O_lambda -> (
              match args with
              | ARG(t,ARG(o,END)) ->
		  let x = Var "x" in
		  let x' = var_to_lf x in
                  Helpers.make_T_Pi t (x, tau (ts_bind env x t) (Substitute.apply_args 0 o (ARG(x',END))))
              | _ -> raise Internal)
          | O_forall -> (
              match args with
              | ARG(u,ARG(u',_)) ->
                  Helpers.make_T_U (nowhere 6 (Helpers.make_U_max u u'))
              | _ -> raise Internal)
          | O_tt -> Helpers.make_T_Pt
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
