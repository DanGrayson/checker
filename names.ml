(** Names of constants, basic dictionary access, and some error handling routines. *)

open Error
open Variables
open Typesystem

exception Internal_expr of lf_expr
exception Unimplemented_expr of lf_expr
exception TypeCheckingFailure of context * position * string
exception TypeCheckingFailure2 of context * position * string * position * string
exception TypeCheckingFailure3 of context * position * string * position * string * position * string

let lf_expr_head_table = [
  T T_Pi, "∏" ; T T_Sigma, "Σ" ; T T_Coprod, "∐" ; 
  O O_lambda, "λ" ; O O_forall, "∀" ;
  U U_next, "next" ; U U_max, "max" ;
  T T_El, "El"  ; T T_U, "U"  ; T T_Pi, "Pi"  ; T T_Sigma, "Sigma" ;
  T T_Pt, "Pt"  ; T T_Coprod, "Coprod"  ; T T_Coprod2, "Coprod2" ;
  T T_Empty, "Empty"  ; T T_IP, "IP"  ; T T_Id, "Id" ;
  O O_u, "u"  ; O O_j, "j"  ; O O_ev, "ev"  ; O O_lambda, "lambda" ;
  O O_forall, "forall"  ; O O_pair, "pair"  ; O O_pr1, "pr1" ;
  O O_pr2, "pr2"  ; O O_total, "total"  ; O O_pt, "pt"  ; O O_pt_r, "pt_r" ;
  O O_tt, "tt"  ; O O_coprod, "coprod"  ; O O_ii1, "ii1"  ; O O_ii2, "ii2" ;
  O O_sum, "sum"  ; O O_empty, "empty"  ; O O_empty_r, "empty_r"  ; O O_c, "c" ;
  O O_ip_r, "ip_r"  ; O O_ip, "ip"  ; O O_paths, "paths"  ; O O_refl, "refl" ;
  O O_J, "J"  ; O O_rr0, "rr0"  ; O O_rr1, "rr1" 
]

let lf_expr_heads = List.map fst lf_expr_head_table

let swap (x,y) = (y,x)

let lf_expr_head_strings = List.map swap lf_expr_head_table

let uhead_to_string h = List.assoc (U h) lf_expr_head_table

let thead_to_string h = List.assoc (T h) lf_expr_head_table

let ohead_to_string h = List.assoc (O h) lf_expr_head_table

let tactic_to_string : tactic_expr -> string = function
  | Tactic_deferred _ -> "$deferred$"
  | Tactic_hole n -> "?" ^ string_of_int n
  | Tactic_name n -> "$" ^ n
  | Tactic_index n -> "$" ^ string_of_int n

let lf_expr_head_to_string = function
  | V v -> vartostring v
  | TAC tac -> tactic_to_string tac
  | h -> "[" ^ List.assoc h lf_expr_head_table ^ "]"

let lf_type_constant_table = [
  F_uexp, "uexp" ;
  F_texp, "texp" ;
  F_oexp, "oexp" ;
  F_istype, "istype" ;
  F_hastype, "hastype" ;
  F_ulevel_equality, "uequal" ;
  F_type_equality, "tequal" ;
  F_object_equality, "oequal" ;
  F_type_uequality, "t-uequal" ;
  F_object_uequality, "o-uequal"
]

let lf_type_head_to_string h = List.assoc h lf_type_constant_table

let lf_type_heads = List.map fst lf_type_constant_table

let string_to_type_constant = List.map swap lf_type_constant_table

let fetch_type env pos v = 
  try List.assoc v env
  with Not_found -> 
    raise (TypeCheckingFailure (env, pos, ("unbound variable: "^vartostring v)))

let label_to_type env pos = function
  | U h -> uhead_to_lf_type h
  | T h -> thead_to_lf_type h
  | O h -> ohead_to_lf_type h
  | V v -> fetch_type env pos v
  | TAC (Tactic_name "defer") -> raise Internal (*?? *)
  | TAC _ -> raise Internal

let var_to_ts v = EVAL(V v,END)

let var_to_lf v = nowhere 1 (var_to_ts v)

let lookup_type (env:context) v = List.assoc v env

let ensure_new_name env pos v =
  try ignore (lookup_type env v);
      raise (MarkedError (pos, "variable already defined: "^vartostring v))
  with Not_found -> ()

let def_bind v (pos:position) o t (env:context) = 
  ensure_new_name env pos v;
  (v, (pos,F_Singleton(o,t))) :: env

let ts_bind (v,t) env = 
  (newfresh (Var "h") , hastype (var_to_lf v) t) :: 
  (v,oexp) ::
  env

let new_hole = 
  let counter = ref 0 in
  fun () -> (
    incr counter;
    EVAL(TAC (Tactic_hole !counter), END))

let hole pos = pos, new_hole()
