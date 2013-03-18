(* -*- coding: utf-8 -*- *)

include Positions
include Variables
include Expressions
include Judgments

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

let var_to_lf_bare v = nowhere 1    (BASIC(V v,END))
let var_to_expr pos v = with_pos pos (BASIC(V v,END))

let id_to_expr_bare v = var_to_lf_bare (Var v)
let id_to_expr pos v = var_to_expr pos (Var v)

let istype t = J_istype @@ [t]				       (* t Type *)
let istype_v pos t = let t = id_to_expr pos t in istype t
let hastype o t = J_hastype @@ [o;t]			       (* o : t *)
let hastype_v t pos o = let o = id_to_expr pos o in hastype o t
let ulevel_equality u u' = J_ulevel_equality @@ [u;u']	       (* u ~ u' *)
let type_uequality t t' = J_type_uequality @@ [t;t']	       (* t ~ t' *)
let type_equality t t' = J_type_equality @@ [t;t']	       (* t = t' *)
let object_uequality o o' t = J_object_uequality @@ [o;o';t]   (* o ~ o' : t *)
let object_equality o o' t = J_object_equality @@ [o;o';t]     (* o = o' : t *)

let istype_embedded_witnesses t = J_istype_witnessed_inside @@ [t] (* t Type *)
let istype_embedded_witnesses_v pos t = let t = id_to_expr pos t in istype_embedded_witnesses t
let witnessed_hastype t o p = J_witnessed_hastype @@ [t;o;p]   (* p : o : t *)
let witnessed_hastype_v t o pos p = let p = id_to_expr pos p in witnessed_hastype t o p
let witnessed_type_equality t t' p = J_witnessed_type_equality @@ [t;t';p] (* p : t = t' *)
let witnessed_type_equality_v t t' pos p = let p = id_to_expr pos p in witnessed_type_equality t t' p
let witnessed_object_equality t o o' p = J_witnessed_object_equality @@ [t;o;o';p] (* p : o = o' : t *)
let witnessed_object_equality_v t o o' pos p = let p = id_to_expr pos p in witnessed_object_equality t o o' p

let texp1 = oexp @-> texp
let texp2 = oexp @-> oexp @-> texp
let texp3 = oexp @-> oexp @-> oexp @-> texp

let oexp1 = oexp @-> oexp
let oexp2 = oexp @-> oexp @-> oexp
let oexp3 = oexp @-> oexp @-> oexp @-> oexp

let wexp_w = oexp @-> wexp @-> wexp
let texp_w = oexp @-> wexp @-> texp
let oexp_w = oexp @-> wexp @-> oexp

let uhead_to_judgment = function	(* optimize later by precomputing the constant return values *)
  | U_next -> uexp @-> uexp
  | U_max -> uexp @-> uexp @-> uexp

let thead_to_judgment = function	(* optimize later by precomputing the constant return values *)
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

let ohead_to_judgment = function	(* optimize later by precomputing the constant return values *)
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

let whead_to_judgment = function	(* optimize later by precomputing the constant return values *)
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

type vartype =
  | SingleVariable of int
  | WitnessPair of int

type vardist = int list list
let head_to_vardist = function (* optimize later by precomputing the constant return values *)
  | W W_wpi2 -> Some (1, [ WitnessPair 0] :: [])
  | W W_wlam -> Some (1, [ WitnessPair 0] :: [])
  | W W_wbeta -> Some (1, [] :: [ WitnessPair 0 ] :: [])
  | T T_Coprod2 -> Some (2, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 1] :: [])
  | O O_ip_r -> Some (5, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [] :: [ SingleVariable 3; SingleVariable 4] :: [] :: [])
  | T T_IP -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [])
  | O O_ev -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_ev' -> Some (1, [] :: [] :: [] :: [ WitnessPair 0 ] :: [])
  | T T_Pi | T T_Sigma | O O_lambda -> Some (1, [] :: [ SingleVariable 0] :: [])
  | T T_Pi' | O O_lambda' -> Some (1, [] :: [ WitnessPair 0] :: [])
  | O O_forall -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pair -> Some (1, [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pr1 | O O_pr2 -> Some (1, [] :: [ SingleVariable 0] :: [] :: [])
  | O O_total -> Some (1, [] :: [] :: [] :: [ SingleVariable 0] :: [])
  | O O_pt_r -> Some (1, [] :: [ SingleVariable 0] :: [])
  | O O_c -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [] :: [] :: [])
  | O O_ip -> Some (3, [] :: [] :: [ SingleVariable 0] :: [ SingleVariable 0; SingleVariable 1] :: [ SingleVariable 0; SingleVariable 1; SingleVariable 2] :: [])
  | O O_J -> Some (2, [] :: [] :: [] :: [] :: [] :: [ SingleVariable 0; SingleVariable 1] :: [])
  | O O_nat_r -> Some(1, [] :: [] :: [] :: [SingleVariable 0] :: [])
  | _ -> None

(** The "kinds" of LF.

    Objects are classified by their type, and (parametrized) types are classified by their kind.

    Notation: constructors starting with "K_" refer to kinds of LF. *)
type lf_kind =
  | K_ulevel
  | K_expression
  | K_primitive_judgment
  | K_judgment
  | K_witnessed_judgment
  | K_Pi of identifier * judgment * lf_kind

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

let tfhead_to_kind = function
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

(** Subordination: see section 2.4 of Mechanizing Meta-theory by Harper and Licata *)
type kind_comparison = K_equal | K_less | K_greater | K_incomparable

let rec ultimate_kind = function
  | K_ulevel
  | K_expression
  | K_judgment
  | K_witnessed_judgment
  | K_primitive_judgment as k -> k
  | K_Pi (v,t,k) -> ultimate_kind k

let rec compare_kinds k l =
  let k = ultimate_kind k in
  let l = ultimate_kind l in
  if k = l then K_equal else
  match k,l with
  | K_primitive_judgment, K_judgment
  | K_judgment,           K_primitive_judgment
      -> K_equal
  | K_ulevel,             _
  | K_expression,         K_judgment
  | K_expression,         K_primitive_judgment
  | K_expression,         K_witnessed_judgment
  | K_primitive_judgment, K_witnessed_judgment
    -> K_less
  | _,                    K_ulevel
  | K_judgment,           K_expression
  | K_primitive_judgment, K_expression
  | K_witnessed_judgment, K_expression
  | K_witnessed_judgment, K_primitive_judgment
    -> K_greater
  | _ -> K_incomparable

(** expr_lists *)

let rec map_expr_list f s = match s with
  | ARG(x,a) -> let x' = f x in let a' = map_expr_list f a in if x' == x && a' == a then s else ARG(x',a')
  | FST a -> let a' = map_expr_list f a in if a' == a then s else FST(a')
  | SND a -> let a' = map_expr_list f a in if a' == a then s else SND(a')
  | END -> s

(** relative indices *)

let rec rel_shift_expr limit shift e =
  match unmark e with
  | BASIC(h,args) ->
      let args' = map_expr_list (rel_shift_expr limit shift) args in
      let h' = rel_shift_head limit shift h in
      if h' == h && args' == args then e else get_pos e, BASIC(h',args')
  | PAIR(x,y) ->
      let x' = rel_shift_expr limit shift x in
      let y' = rel_shift_expr limit shift y in
      if x' == x && y' == y then e else get_pos e, PAIR(x',y')
  | TEMPLATE(v, body) ->
      let limit = limit + 1 in
      let body' = rel_shift_expr limit shift body in
      if body' == body then e else get_pos e, TEMPLATE(v, body')

and rel_shift_head limit shift h = 
  match h with
  | V (Rel i) when i >= limit -> V (Rel (shift+i))
  | _ -> h

and rel_shift_type limit shift t =
  match unmark t with
  | J_Pi(v,a,b) ->
      let a' = rel_shift_type limit shift a in
      let limit = limit + 1 in
      let b' = rel_shift_type limit shift b in
      if a' == a && b' == b then t else get_pos t, J_Pi(v,a',b')
  | J_Sigma(v,a,b) ->
      let a' = rel_shift_type limit shift a in
      let limit = limit + 1 in
      let b' = rel_shift_type limit shift b in
      if a' == a && b' == b then t else get_pos t, J_Sigma(v,a',b')
  | J_Basic(label,args) ->
      let args' = List.map (rel_shift_expr limit shift) args in
      if args' == args then t else get_pos t, J_Basic(label, args')
  | J_Singleton(e,u) ->
      let e' = rel_shift_expr limit shift e in
      let u' = rel_shift_type limit shift u in
      if e' == e && u' == u then t else get_pos t, J_Singleton(e',u')

let rel_shift_expr shift e = if shift = 0 then e else rel_shift_expr 0 shift e

let rel_shift_head shift h = if shift = 0 then h else rel_shift_head 0 shift h

let rel_shift_type shift t = if shift = 0 then t else rel_shift_type 0 shift t

(** Contexts. *)

module MapString = Map.Make(String)
module MapIdentifier = Map.Make(Identifier)

type tts_judgment = TTS_istype | TTS_hastype of expr

type environment = {
    state : int;
    local_tts_context : (string * tts_judgment) list;
    global_tts_context : tts_judgment MapString.t;
    local_lf_context : (identifier * judgment) list;
    global_lf_context : judgment MapIdentifier.t;
  }

let empty_environment = {
  state = 0;
  local_tts_context = [];
  global_tts_context = MapString.empty;
  local_lf_context = [];
  global_lf_context = MapIdentifier.empty;
}

let interactive = ref false

let incr_state env =
  if !interactive
  then { env with state = env.state + 1 }
  else env

let local_lf_bind env v t = { env with local_lf_context = (v,t) :: env.local_lf_context }

let local_lf_fetch env i = 			(* (Rel i) *)
  try rel_shift_type (i+1) (snd (List.nth env.local_lf_context i))
  with Failure "nth" -> raise Not_found

let global_lf_bind env pos name t = 
  if MapIdentifier.mem name env.global_lf_context then raise (MarkedError (pos, "identifier already defined: " ^ idtostring name));
  { env with global_lf_context = MapIdentifier.add name t env.global_lf_context }

let global_lf_fetch env name = MapIdentifier.find name env.global_lf_context

let lf_fetch env = function
  | Var name -> global_lf_fetch env name
  | Rel i -> local_lf_fetch env i

let local_tts_declare_type   env name   = { env with local_tts_context = (name,TTS_istype   ) :: env.local_tts_context }

let local_tts_declare_object env name t = { env with local_tts_context = (name,TTS_hastype t) :: env.local_tts_context }

let global_tts_declare_type env pos name = 
  if MapString.mem name env.global_tts_context then raise (MarkedError (pos, "variable already defined: " ^ name));
  { env with global_tts_context = MapString.add name TTS_istype env.global_tts_context }

let global_tts_declare_object env pos name t = 
  if MapString.mem name env.global_tts_context then raise (MarkedError (pos, "variable already defined: " ^ name));
  { env with global_tts_context = MapString.add name (TTS_hastype t) env.global_tts_context }

let ts_bind env v t = 
  if isid v then local_tts_declare_object env (id_to_name v) t else raise Internal

let local_tts_fetch env i =			(* (Rel i) *)
  (* note: each TTS_hastype consumes two relative indices, whereas each TTS_istype consumes only one; that should change *)
  let rec repeat shift i context =
    match context with
    | (_,TTS_istype) :: context -> if i = 0 then TTS_istype else repeat (shift+1) (i-1) context
    | (_,TTS_hastype t) :: context -> if i = 0 || i = 1 then TTS_hastype (rel_shift_expr shift t) else repeat (shift+2) (i-2) context
    | [] -> raise Not_found
  in repeat 2 i env.local_tts_context

let global_tts_fetch env name = MapString.find name env.global_tts_context

let global_tts_fetch_type env name =
  match
    global_tts_fetch env name
  with
  | TTS_istype -> raise Not_found
  | TTS_hastype t -> t

let is_tts_type_variable env name =
  try
    match
      global_tts_fetch env name
    with
    | TTS_istype -> true
    | TTS_hastype _ -> false
  with
  | Not_found -> false

let tts_fetch env = function
  | Var id -> global_tts_fetch env (id_to_name id)
  | Rel i -> local_tts_fetch env i

let tts_fetch_type env name =
  match tts_fetch env name with
  | TTS_istype -> raise Not_found
  | TTS_hastype t -> t

let ts_fetch env v = 
  match tts_fetch env v with
  | TTS_hastype t -> t
  | TTS_istype -> raise Internal

let first_var env =
  match env.local_tts_context with
  | (name,_) :: _ -> id name
  | _ -> raise Internal

let first_w_var env =
  match env.local_tts_context with
  | (name,_) :: _ -> idw name
  | _ -> raise Internal

type uContext = UContext of var marked list * (expr * expr) marked list

let empty_uContext = UContext([],[])

(** Tactics. *)

type surrounding_component =
  | S_expr_list of int			 (* argument position, starting with 1 *)
  | S_expr_list' of int			 (* argument position, starting with 1 *)
	* expr_head			 (* head *)
	* expr_list				 (* arguments passed, in reverse order, possibly updated by tactics *)
	* expr_list				 (* arguments coming *)
  | S_type_args of int                   (* argument position, starting with 1 *)
	* judgment list			 (* arguments passed, possibly updated by tactics *)
  | S_type_family_args of int            (* argument position, starting with 1 *)
	* expr list			 (* arguments passed, in reverse order, possibly updated by tactics *)
  | S_projection of int
  | S_body

type surrounding = (environment * surrounding_component * expr option * judgment option) list

type tactic_return =
  | TacticFailure
  | TacticSuccess of expr

type tactic_function =
       surrounding         (* the ambient BASIC(...), if any, and the index among its head and arguments of the hole *)
    -> environment						      (* the active context *)
    -> position							      (* the source code position of the tactic hole *)
    -> judgment							      (* the type of the hole, e.g., [texp] *)
    -> expr_list							      (* the arguments *)
 -> tactic_return						      (* the proffered expression *)

let tactics : (string * tactic_function) list ref = ref []

let add_tactic (name,f) = tactics := (name,f) :: !tactics

(*
  Local Variables:
  compile-command: "make -C .. src/typesystem.cmo "
  End:
 *)
