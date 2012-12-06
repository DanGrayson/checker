(** Names of constants, basic dictionary access, and some error handling routines. *)

open Error
open Typesystem

exception Internal_expr of lf_expr
exception Unimplemented_expr of lf_expr
exception TypeCheckingFailure of context * position * string
exception TypeCheckingFailure2 of context * position * string * position * string
exception TypeCheckingFailure3 of context * position * string * position * string * position * string

let uhead_to_string = function
  | U_next -> "next" | U_max -> "max"

let thead_to_string = function
  | T_El -> "El"  | T_U -> "U"  | T_Pi -> "Pi"  | T_Sigma -> "Sigma"
  | T_Pt -> "Pt"  | T_Coprod -> "Coprod"  | T_Coprod2 -> "Coprod2"
  | T_Empty -> "Empty"  | T_IP -> "IP"  | T_Id -> "Id"

let ohead_to_string = function
  | O_u -> "u"  | O_j -> "j"  | O_ev -> "ev"  | O_lambda -> "lambda"
  | O_forall -> "forall"  | O_pair -> "pair"  | O_pr1 -> "pr1"
  | O_pr2 -> "pr2"  | O_total -> "total"  | O_pt -> "pt"  | O_pt_r -> "pt_r"
  | O_tt -> "tt"  | O_coprod -> "coprod"  | O_ii1 -> "ii1"  | O_ii2 -> "ii2"
  | O_sum -> "sum"  | O_empty -> "empty"  | O_empty_r -> "empty_r"  | O_c -> "c"
  | O_ip_r -> "ip_r"  | O_ip -> "ip"  | O_paths -> "paths"  | O_refl -> "refl"
  | O_J -> "J"  | O_rr0 -> "rr0"  | O_rr1 -> "rr1"

let vartostring = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "$" ^ (string_of_int i)
  | VarUnused -> "_"
  | VarDefined (name,aspect) -> "[" ^ name ^ "." ^ (string_of_int aspect) ^ "]"

let lf_expr_head_to_string = function
  | V v -> vartostring v
  | U h -> "[" ^ uhead_to_string h ^ "]"
  | T h -> "[" ^ thead_to_string h ^ "]"
  | O h -> "[" ^ ohead_to_string h ^ "]"

let lf_expr_heads = List.concat [
  List.map (fun h -> U h) uheads;
  List.map (fun h -> T h) theads;
  List.map (fun h -> O h) oheads
]

let string_to_label = 
  let a = List.map (fun h -> lf_expr_head_to_string h, h) lf_expr_heads in
  let b = [
    ("[∏]", T T_Pi);
    ("[Σ]", T T_Sigma);
    ("[∐]", T T_Coprod);
    ("[λ]", O O_lambda);
    ("[∀]", O O_forall)] in
  List.concat [a;b]

let lf_type_head_to_string = function
  | F_uexp -> "uexp"
  | F_texp -> "texp"
  | F_oexp -> "oexp"
  | F_istype -> "istype"
  | F_hastype -> "hastype"
  | F_ulevel_equality -> "uequal"
  | F_type_equality -> "tequal"
  | F_object_equality -> "oequal"
  | F_type_uequality -> "t-uequal"
  | F_object_uequality -> "o-uequal"

let tfhead_strings = List.map (fun x -> lf_type_head_to_string x, x) lf_type_heads

let tactic_to_string : tactic_expr -> string = function
  | Q_name n -> "$" ^ n
  | Q_index n -> "$" ^ (string_of_int n)

let fetch_type env pos v = 
  try List.assoc v env
  with Not_found -> 
    raise (TypeCheckingFailure (env, pos, ("unbound variable: "^(vartostring v))))

let label_to_type env pos = function
  | U h -> uhead_to_lf_type h
  | T h -> thead_to_lf_type h
  | O h -> ohead_to_lf_type h
  | V v -> fetch_type env pos v

let rec get_pos_lf (x:lf_expr) =
  match x with
  | Phi x -> get_pos x
  | LAMBDA(x,b) -> get_pos_lf b

let var_to_ts v = APPLY(V v,[])

let var_to_lf v = Phi (nowhere 1 (var_to_ts v))

let lookup_type env v = List.assoc v env

let def_bind v (pos:position) o t (env:context) = (v, (pos,F_Singleton(o,t))) :: env

(* raise an exception when a certain fresh variable is generated *)
let genctr_trap = 0

let newfresh = 
  let genctr = ref 0 in 
  let newgen x = (
    incr genctr;
    if !genctr = genctr_trap then raise DebugMe;
    if !genctr < 0 then raise GensymCounterOverflow;
    VarGen (!genctr, x)) in
  fun v -> match v with 
  | Var x | VarGen(_,x) -> newgen x
  | VarDefined _ | VarUnused -> raise Internal

let ts_bind (v,t) env = match v with
  | VarUnused -> env
  | v -> 
      (newfresh (Var "h") , hastype (var_to_lf v) (Phi t)) :: 
      (v,oexp) :: 
      env

let new_hole = 
  let counter = ref 0 in
  function () -> (
    let h = EmptyHole !counter in
    incr counter;
    h)
