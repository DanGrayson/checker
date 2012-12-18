open Printf
open Printer
open Error
open Variables
open Typesystem
open Names

let rec get_ts_type v env = 
  if !sigma_mode then raise Internal;
  match env with
  | (_, (pos, F_APPLY(F_hastype,[(_,APPLY(V v',END)); t]))) :: env -> if v = v' then t else get_ts_type v env
  | _ :: env -> get_ts_type v env
  | _ -> raise Not_found

let rec get_ts_type_2 v env =
  if not (!sigma_mode) then raise Internal;
  match unmark (List.assoc v env) with
  | F_Sigma(_,_,(_,F_APPLY(F_hastype,[(_,APPLY(V v',END)); t]))) -> t
  | _ -> raise Internal

let rec tau (pos:position) (env:context) e : lf_expr = 
  let pos = get_pos e in
  match unmark e with
  | APPLY(V v,END) -> (
      try get_ts_type v env
      with Not_found -> raise (TypeCheckingFailure(env, [pos, "variable not in TS context: " ^ vartostring v])))
  | APPLY(V v,CAR END) -> (		(* pi1 v *)
      if !debug_mode then printf " v = %a\n%!" _v v;
      if !debug_mode then print_context (Some 4) stderr env;
      try get_ts_type_2 v env
      with Not_found -> raise (TypeCheckingFailure(env, [pos, "variable not in TS context: " ^ vartostring v])))
  | APPLY(h,args) -> with_pos pos (
      match h with
      | TAC _ -> raise NotImplemented
      | V v -> raise NotImplemented
      | FUN _ -> raise NotImplemented
      | U uh -> raise Internal          (* u-expression doesn't have a type *)
      | T th -> raise Internal          (* t-expression doesn't have a type *)
      | O oh -> (
          match oh with
          | O_u -> (
              match args with 
              | ARG(u,END) -> Helpers.make_T_U (pos, (Helpers.make_U_next u))
              | _ -> raise Internal)
          | O_j -> (
              match args with 
              | ARG(m1,ARG(m2,END)) -> 
                  Helpers.make_T_Pi 
                    (with_pos_of m1 (Helpers.make_T_U m1))
                    (newunused(), (with_pos_of m2 (Helpers.make_T_U m2)))
              | _ -> raise Internal)
          | O_ev -> (
              match args with 
              | ARG(f,ARG(o,ARG((_,LAMBDA(x,t)),END))) ->
                  unmark (Substitute.subst (x,o) t)
              | _ -> raise Internal)
          | O_lambda -> (
              match args with 
              | ARG(t,ARG((_,LAMBDA(x,o)),END)) ->
                  Helpers.make_T_Pi t (x, tau pos (ts_bind (x,t) env) o)
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
            -> raise NotImplemented
         ) )
  | _ -> raise Internal

let tau env e = tau (no_pos 2) env e

(* 
  Local Variables:
  compile-command: "make tau.cmo "
  End:
 *)
