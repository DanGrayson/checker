(** Expressions *) (* -*- coding: utf-8 -*- *)

type var =
  | Rel of int			(* deBruijn index, starting with 0 *)

let vartostring = function
  | Rel i -> string_of_int i ^ "^"	(* raw form *)

type expr_head = 

    Var of var

  | U_next | U_max

  | T_El | T_U | T_Pi | T_Sigma | T_Pt
  | T_Coprod | T_Coprod2 | T_Empty | T_IP | T_Id

  | O_u | O_j | O_ev | O_lambda | O_forall | O_pair | O_pr1
  | O_pr2 | O_total | O_pt | O_pt_r | O_tt | O_coprod | O_ii1 | O_ii2 | O_sum
  | O_empty | O_empty_r | O_c | O_ip_r | O_ip | O_paths | O_refl | O_J | O_rr0
  | O_rr1 | O_nat | O_nat_r | O_O | O_S | O_conv

  | W_Refl | W_Symm | W_Trans | W_refl | W_symm | W_trans
  | W_conveq | W_Eleq | W_pi1 | W_pi2 | W_lam | W_l1 | W_l2 | W_ev
  | W_evt1 | W_evt2 | W_evf | W_evo | W_beta | W_eta

type expr =
  | BASIC of expr_head * expr_list
and expr_list =
  | ARG of int * expr * expr_list	(* the integer gives the number of variables bound in expr *)
  | END

let ( @ ) h s = BASIC(h,s)
let ( ** ) x s = ARG(0,x,s)		(* right associative *)
let ( **. ) x s = ARG(1,x,s)
let ( **.. ) x s = ARG(2,x,s)
let ( **... ) x s = ARG(3,x,s)
let var_to_expr v = (Var v) @ END

let rec expr_equality x y = 
  match x,y with
  | BASIC(O_conv,ARG(_,x',_)),_ -> expr_equality x' y
  | _,BASIC(O_conv,ARG(_,y',_)) -> expr_equality x y'
  | BASIC(h,a),BASIC(k,b) -> h = k && expr_list_equality (a,b)
and expr_list_equality = function
  | ARG(i,x,a'),ARG(j,y,b') -> i = j && expr_equality x y && expr_list_equality (a',b')
  | END,END -> true
  | _,_ -> false

type jgmt_head = J_istype | J_hastype | J_type_equality | J_object_equality

type judgment = 
  | J of jgmt_head * expr list
	(* J(J_istype,[t]) represents |- t type
	   J(J_hastype,[t;o]) represents |- o : t
	   J(J_type_equality,[t;t';p]) represents |- p : t = t' 
	     Here p is a witness that allows the derivation tree
	     to be recovered.
	   J(J_object_equality,[t;o;o';p]) represents |- p : o = o' : t 
	     Here p is a witness that allows the derivation tree
	     to be recovered.
	   If the last expr in the list is missing, then it represents a
	     hypothesis, if present, a conclusion and definition. *)
  | J_Pi of judgment * judgment	(* (j,k) represents the judgment that j entails k.
				   Here j would usually have the last expr missing, and
				   the corresponding variable is bound in k.
				   Use j=>k as an abbreviation. *)

(*
  Local Variables:
  compile-command: "make -C .. src/expressions.cmo "
  End:
 *)
