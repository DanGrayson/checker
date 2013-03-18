(** Signatures *)

include Kinds

(** Signatures for expressions *)

let ( @@ ) f x : judgment = nowhere 3 (J_Basic(f,x))

let uexp = J_uexp @@ []
let wexp = J_wexp @@ []
let texp = J_texp @@ []
let oexp = J_oexp @@ []

let rec arrow_good_var_name t =
  match unmark t with 
  | J_Basic(J_istype,_) -> id "i"
  | J_Basic(J_hastype,_) -> id "h"
  | J_Basic(J_type_equality,_) -> id "teq"
  | J_Basic(J_object_equality,_) -> id "oeq"
  | J_Pi(_,_,u) -> arrow_good_var_name u
  | _ -> id "x"

let arrow a b = nowhere 4 (J_Pi(arrow_good_var_name a, a, b))
let ( @-> ) = arrow

let texp1 = oexp @-> texp
let texp2 = oexp @-> oexp @-> texp
let texp3 = oexp @-> oexp @-> oexp @-> texp

let oexp1 = oexp @-> oexp
let oexp2 = oexp @-> oexp @-> oexp
let oexp3 = oexp @-> oexp @-> oexp @-> oexp

let wexp_w = oexp @-> wexp @-> wexp
let texp_w = oexp @-> wexp @-> texp
let oexp_w = oexp @-> wexp @-> oexp

let uhead_to_signature = function	(* optimize later by precomputing the constant return values *)
  | U_next -> uexp @-> uexp
  | U_max -> uexp @-> uexp @-> uexp

let thead_to_signature = function	(* optimize later by precomputing the constant return values *)
  | T_El -> oexp @-> texp
  | T_El' -> oexp @-> wexp @-> texp
  | T_U -> uexp @-> texp
  | T_U' -> texp
  | T_Pi -> texp @-> texp1 @-> texp
  | T_Pi' -> texp @-> texp_w @-> texp
  | T_Sigma -> texp @-> texp1 @-> texp
  | T_Pt -> texp
  | T_Coprod -> texp @-> texp @-> texp
  | T_Coprod2 -> texp @-> texp @-> texp1 @-> texp1 @-> texp
  | T_Empty -> texp
  | T_IP -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> texp
  | T_Id -> texp @-> oexp @-> oexp @-> texp
  | T_Proof -> wexp @-> oexp @-> texp @-> texp

let ohead_to_signature = function	(* optimize later by precomputing the constant return values *)
  | O_u -> uexp @-> oexp
  | O_j -> uexp @-> uexp @-> oexp
  | O_ev -> oexp @-> oexp @-> texp @-> texp1 @-> oexp
  | O_ev' -> oexp @-> oexp @-> texp @-> texp_w @-> oexp
  | O_lambda -> texp @-> oexp1 @-> oexp
  | O_lambda' -> texp @-> oexp_w @-> oexp
  | O_forall -> uexp @-> uexp @-> oexp @-> oexp1 @-> oexp
  | O_pair -> oexp @-> oexp @-> texp1 @-> oexp
  | O_pr1 -> texp @-> texp1 @-> oexp @-> oexp
  | O_pr2 -> texp @-> texp1 @-> oexp @-> oexp
  | O_total -> uexp @-> uexp @-> oexp @-> oexp1 @-> oexp
  | O_pt -> oexp
  | O_pt_r -> oexp @-> texp1 @-> oexp
  | O_tt -> oexp
  | O_coprod -> uexp @-> uexp @-> oexp @-> oexp @-> oexp
  | O_ii1 -> texp @-> texp @-> oexp @-> oexp
  | O_ii2 -> texp @-> texp @-> oexp @-> oexp
  | O_sum -> texp @-> texp @-> oexp @-> oexp @-> oexp @-> texp1 @-> oexp
  | O_empty -> oexp
  | O_empty_r -> texp @-> oexp @-> oexp
  | O_c -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> oexp @-> oexp @-> oexp
  | O_ip_r -> texp @-> oexp @-> texp1 @-> texp2 @-> oexp3 @-> oexp @-> texp2 @-> oexp @-> oexp
  | O_ip -> oexp @-> oexp @-> oexp1 @-> oexp2 @-> oexp3 @-> oexp
  | O_paths -> uexp @-> oexp @-> oexp @-> oexp @-> oexp
  | O_refl -> texp @-> oexp @-> oexp
  | O_J -> texp @-> oexp @-> oexp @-> oexp @-> oexp @-> texp2 @-> oexp
  | O_rr0 -> uexp @-> uexp @-> oexp @-> oexp @-> oexp @-> oexp
  | O_rr1 -> uexp @-> oexp @-> oexp @-> oexp
  | O_nat -> oexp
  | O_O -> oexp
  | O_S -> oexp
  | O_nat_r -> oexp @-> oexp @-> oexp @-> texp1 @-> oexp

let whead_to_signature = function	(* optimize later by precomputing the constant return values *)
  | W_Wrefl -> wexp
  | W_Wsymm -> wexp @-> wexp
  | W_Wtrans -> wexp @-> wexp @-> texp @-> wexp
  | W_wrefl -> wexp @-> wexp @-> wexp
  | W_wsymm -> wexp @-> wexp
  | W_wtrans -> wexp @-> wexp @-> oexp @-> wexp
  | W_wconv -> wexp @-> wexp @-> wexp
  | W_wconveq -> wexp @-> wexp @-> texp @-> wexp
  | W_weleq -> wexp @-> wexp
  | W_wpi1 -> wexp @-> wexp
  | W_wpi2 -> wexp_w @-> wexp
  | W_wlam -> wexp_w @-> wexp
  | W_wl1 -> wexp @-> wexp @-> wexp
  | W_wl2 -> wexp @-> wexp
  | W_wev -> wexp @-> wexp @-> wexp
  | W_wevt1 -> wexp @-> wexp @-> wexp @-> wexp
  | W_wevt2 -> wexp @-> wexp @-> wexp @-> wexp
  | W_wevf -> wexp @-> wexp @-> wexp
  | W_wevo -> wexp @-> wexp @-> wexp @-> wexp
  | W_wbeta -> wexp @-> wexp_w @-> wexp
  | W_weta -> wexp @-> wexp

(** Signatures for judgments *)

let ( @@-> ) a b = K_Pi(arrow_good_var_name a, a, b)

let istype_kind = texp @@-> K_primitive_judgment
let hastype_kind = oexp @@-> texp @@-> K_judgment
let type_equality_kind = texp @@-> texp @@-> K_judgment
let object_equality_kind = oexp @@-> oexp @@-> texp @@-> K_judgment
let ulevel_equality_kind = uexp @@-> uexp @@-> K_judgment
let type_uequality_kind = texp @@-> texp @@-> K_primitive_judgment
let object_uequality_kind = oexp @@-> oexp @@-> texp @@-> K_primitive_judgment
let istype_witnessed_internally_kind = texp @@-> K_witnessed_judgment
let witnessed_hastype_kind = texp @@-> oexp @@-> wexp @@-> K_witnessed_judgment
let witnessed_type_equality_kind = texp @@-> texp @@-> wexp @@-> K_witnessed_judgment
let witnessed_object_equality_kind = texp @@-> oexp @@-> oexp @@-> wexp @@-> K_witnessed_judgment

let jhead_to_kind = function
  | J_uexp -> K_ulevel
  | J_wexp | J_texp | J_oexp -> K_expression
  | J_istype -> istype_kind
  | J_hastype -> hastype_kind
  | J_ulevel_equality -> ulevel_equality_kind
  | J_type_equality -> type_equality_kind
  | J_object_equality -> object_equality_kind
  | J_type_uequality -> type_uequality_kind
  | J_object_uequality -> object_uequality_kind
  | J_istype_witnessed_inside -> istype_witnessed_internally_kind
  | J_witnessed_hastype -> witnessed_hastype_kind
  | J_witnessed_type_equality -> witnessed_type_equality_kind
  | J_witnessed_object_equality -> witnessed_object_equality_kind
