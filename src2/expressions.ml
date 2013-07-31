(* -*- coding: utf-8 -*- *)

(** Expressions *)
include Variables

type uHead = | U_next | U_max
type tHead = | T_El | T_U | T_Pi | T_Sigma | T_Pt
             | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id
type oHead = | O_u | O_j | O_ev | O_lambda | O_forall | O_pair | O_pr1
	     | O_pr2 | O_total | O_pt | O_pt_r | O_tt | O_coprod | O_ii1 | O_ii2 | O_sum
	     | O_empty | O_empty_r | O_c | O_ip_r | O_ip | O_paths | O_refl | O_J | O_rr0
	     | O_rr1 | O_nat | O_nat_r | O_O | O_S
type wHead = | W_Wrefl | W_Wsymm | W_Wtrans | W_wrefl | W_wsymm | W_wtrans | W_wconv
	     | W_wconveq | W_weleq | W_wpi1 | W_wpi2 | W_wlam | W_wl1 | W_wl2 | W_wev
	     | W_wevt1 | W_wevt2 | W_wevf | W_wevo | W_wbeta | W_weta

type expr_head = | U of uHead | T of tHead | O of oHead | W of wHead | V of var

type expr =
  | BASIC of expr_head * expr_list
and expr_list =
  | ARG of int * expr * expr_list	(* the integer gives the number of variables bound here *)
  | END

(** Functions *)

let var_to_expr v = BASIC(V v,END)

(*
  Local Variables:
  compile-command: "make -C .. src/expressions.cmo "
  End:
 *)
