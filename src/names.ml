(** Names of constants, basic dictionary access, and some error handling routines. *)

open Error
open Variables
open Typesystem

exception Internal_expr of lf_expr
exception Unimplemented_expr of lf_expr
exception TypeCheckingFailure of environment * surrounding * (position * string) list

let lf_expr_head_table = [
  T T_Pi, "∏"; O O_lambda, "λ"; O O_ev, "ev";
  O O_forall, "forall";
  T T_El, "El";
  T T_Id, "Id"; O O_paths, "paths"; O O_refl, "refl"; O O_J, "J";
  T T_Sigma, "Σ"; O O_pair, "pair"; O O_pr1, "pr1"; O O_pr2, "pr2"; O O_total, "total";
  T T_Pt, "Pt"; O O_pt, "pt"; O O_pt_r, "pt_r"; O O_tt, "tt";
  T T_Coprod, "∐"; T T_Coprod, "Coprod"; T T_Coprod2, "Coprod2";
  T T_Empty, "Empty"; O O_empty, "empty"; O O_empty_r, "empty_r";
  T T_IP, "IP"; O O_ip_r, "ip_r"; O O_ip, "ip"; O O_c, "c";
  O O_coprod, "coprod"; O O_ii1, "ii1"; O O_ii2, "ii2";
  O O_sum, "sum";
  U U_next, "next"; U U_max, "max"; T T_U, "U"; T T_U', "U'"; O O_u, "u"; O O_j, "j";
  O O_rr0, "rr0"; O O_rr1, "rr1";
  T T_Pi, "Pi"; T T_Sigma, "Sigma"; O O_lambda, "lambda";
  T T_Proof, "Proof";
  T T_El', "El'"; T T_Pi', "Pi'"; T T_Pi', "∏'";
  O O_nat, "nat"; O O_nat_r, "nat_r"; O O_O, "O"; O O_S, "S";
  O O_lambda', "λ'"; O O_lambda', "lambda'"; O O_ev', "ev'";
  W W_Wrefl, "Wrefl"; W W_Wsymm, "Wsymm"; W W_Wtrans, "Wtrans";
  W W_wrefl, "wrefl"; W W_wsymm, "wsymm"; W W_wtrans, "wtrans"; W W_wconv, "wconv";
  W W_wconveq, "wconveq"; W W_weleq, "weleq"; W W_wpi1, "wpi1"; W W_wpi2, "wpi2";
  W W_wlam, "wlam"; W W_wl1, "wl1"; W W_wl2, "wl2"; W W_wev, "wev";
  W W_wevt1, "wevt1"; W W_wevt2, "wevt2"; W W_wevf, "wevf"; W W_wevo, "wevo";
  W W_wbeta, "wbeta"; W W_weta, "weta"
]

let expr_head_to_string h = List.assoc h lf_expr_head_table

let lf_expr_heads = List.map fst lf_expr_head_table

let swap (x,y) = (y,x)

let lf_expr_head_strings = List.map swap lf_expr_head_table

let rec tactic_to_string = function
  | Tactic_name n -> if n = "default" then "_" else "$" ^ n
  | Tactic_sequence(x,rest) -> "$(" ^ tactic_to_string x ^ ";" ^ tactic_to_string rest ^ ")"
  | Tactic_index n -> "$" ^ string_of_int n

let lf_type_constant_table = [
  F_uexp, "uexp" ;
  F_texp, "texp" ;
  F_oexp, "oexp" ;
  F_istype, "istype" ;
  F_hastype, "hastype" ;
  F_ulevel_equality, "uequal" ;
  F_type_equality, "tequal" ;
  F_object_equality, "oequal" ;
  F_type_uequality, "tuequal" ;
  F_object_uequality, "ouequal";
  F_a_type, "Texp";
  F_obj_of_type, "Oexp";
  F_judged_type_equal, "Tequal";
  F_judged_obj_equal, "Oequal";
  F_wexp, "wexp";

  F_istype_witness, "istype_witness";
  F_hastype_witness, "hastype_witness";
  F_type_equality_witness, "type_equality_witness";
  F_object_equality_witness, "object_equality_witness";

  F_witnessed_istype, "witnessed_istype";
  F_witnessed_hastype, "witnessed_hastype";
  F_witnessed_type_equality, "witnessed_type_equality";
  F_witnessed_object_equality, "witnessed_object_equality";
]

let lf_kind_constant_table = [
  K_ulevel, "ulevel";
  K_expression, "expression";
  K_judgment, "judgment";
  K_primitive_judgment, "primitive_judgment";
  K_judged_expression, "judged_expression";
  K_witnessed_judgment, "witnessed_judgment"
]

let lf_type_head_to_string h = List.assoc h lf_type_constant_table

let lf_type_heads = List.map fst lf_type_constant_table

let string_to_type_constant = List.map swap lf_type_constant_table

let marked_var_to_lf (pos,v) = pos, APPLY(V v,END)

let var_to_lf_pos pos v = with_pos pos (APPLY(V v,END))

let head_to_type env pos = function
  | W h -> whead_to_lf_type h
  | U h -> uhead_to_lf_type h
  | T h -> thead_to_lf_type h
  | O h -> ohead_to_lf_type h
  | V (VarRel i) -> snd (List.nth env.lf_context i)
  | V (Var _ as v) -> (
      try VarMap.find v env.global_lf_context
      with Not_found ->
	trap();
	raise (TypeCheckingFailure (env, [], [pos, "unbound variable: " ^ vartostring v])))
  | V _ -> raise Internal
  | TAC _ -> (trap(); raise Internal)

let ensure_new_name env pos v =
  if VarMap.mem v env.global_lf_context then
    raise (MarkedError (pos, "variable already defined: " ^ vartostring v))

let axiom_bind v (pos:position) t (env:environment) =
  ensure_new_name env pos v;
  global_lf_bind env v t

let def_bind v (pos:position) o t (env:environment) =
  axiom_bind v pos (with_pos pos (F_Singleton(o,t))) env

(*
  Local Variables:
  compile-command: "make -C .. src/names.cmo "
  End:
 *)
