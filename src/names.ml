(** Names of constants, basic dictionary access, and some error handling routines. *)

open Typesystem

exception Internal_expr of expr
exception Unimplemented_expr of expr
exception TypeCheckingFailure of environment * surrounding * (position * string) list

let expr_head_table = [
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

let tts_mode_expr_head_table = List.flatten [
  [ T T_U', "U";  T T_U, "U$";
    T T_El', "El"; T T_El, "El$";
    T T_Pi', "Pi"; T T_Pi, "Pi$";
    T T_Pi', "∏"; O O_lambda', "λ"; O O_lambda, "lambda$";
    O O_lambda', "lambda"; O O_ev', "ev" ; O O_ev, "ev$"
  ]; 
  expr_head_table ]

let ts_mode = ref true

let expr_heads = List.map fst expr_head_table

let expr_head_table() = if !ts_mode then expr_head_table else tts_mode_expr_head_table

let expr_head_to_string h = List.assoc h (expr_head_table())

let rec tactic_to_string = function
  | n -> if n = "default" then "_" else "$" ^ n

let judgment_constant_table = [
  J_uexp, "uexp" ;
  J_texp, "texp" ;
  J_oexp, "oexp" ;
  J_istype, "istype" ;
  J_hastype, "hastype" ;
  J_ulevel_equality, "uequal" ;
  J_type_equality, "tequal" ;
  J_object_equality, "oequal" ;
  J_type_uequality, "tuequal" ;
  J_object_uequality, "ouequal";
  J_wexp, "wexp";

  J_istype_witnessed_inside, "istype_witnessed_inside";
  J_witnessed_hastype, "witnessed_hastype";
  J_witnessed_type_equality, "witnessed_type_equality";
  J_witnessed_object_equality, "witnessed_object_equality";
]

let kind_constant_table = [
  K_ulevel, "ulevel";
  K_term, "term";
  K_witnessed_judgment, "witnessed_judgment";
  K_derivation_tree_judgment, "derivation_tree_judgment";
  K_primitive_judgment, "primitive_judgment";
]

let judgment_head_to_string h = List.assoc h judgment_constant_table

let judgment_heads = List.map fst judgment_constant_table

let marked_var_to_lf (pos,v) = pos, BASIC(V v,END)

let ensure_new_name env pos name =
  if MapIdentifier.mem name env.global_lf_context then
    raise (MarkedError (pos, "identifier already defined: " ^ idtostring name))

let axiom_bind name pos t env =
  global_lf_bind env pos name t

let def_bind name (pos:position) o t env =
  axiom_bind name pos (with_pos pos (J_Singleton(o,t))) env

(*
  Local Variables:
  compile-command: "make -C .. src/names.cmo "
  End:
 *)
