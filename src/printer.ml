(** Functions for converting expressions to strings for printing *)

let enable_variable_prettification = true

open Error
open Helpers
open Typesystem
open Names
open Printf

let space x = " " ^ x

let ( <<- ) f g x = f (g x)

let concat = String.concat ""

let concatl = concat <<- List.flatten

(** Lists of free variables. *)

let rec names_in_list p_arg args = List.flatten (List.map p_arg args)

let rec names_in_expr_list args =
  match args with
  | ARG(x,args) -> names_in_expr x @ names_in_expr_list args
  | FST args | SND args -> names_in_expr_list args
  | END -> []

and names_in_head = function V (Var v) -> [id_to_name v] | V (Rel _) | U _ | T _ | W _ | O _ | TACTIC _ -> []

and names_in_expr (pos,e) = match e with
  | TEMPLATE(x,body) -> names_in_expr body
  | PAIR(x,y) -> names_in_expr x @ names_in_expr y
  | BASIC(h,args) -> names_in_head h @ names_in_expr_list args

and names_in_type (pos,t) = match t with
  | J_Pi(v,t,u) | J_Sigma(v,t,u) -> names_in_type t @ names_in_type u
  | J_Singleton(x,t) -> names_in_expr x @ names_in_type t
  | J_Basic(hd,args) -> names_in_list names_in_expr args

let rec names_in_kind = function
  | K_basic_judgment | K_ulevel | K_syntactic_judgment | K_witnessed_judgment | K_derived_judgment -> []
  | K_Pi(v,t,k) -> names_in_type t @ names_in_kind k

(** Whether [Rel 0] occurs as a bound variable in an expression. *)

let rec rel_occurs_in_head shift h =
  match h with
  | V (Rel i) -> i = shift
  | V (Var _) | W _ | U _ | T _ | O _ | TACTIC _ -> false

and rel_occurs_in_expr shift e =
  match unmark e with
  | TEMPLATE(v,body) -> rel_occurs_in_expr (shift+1) body
  | PAIR(x,y) -> rel_occurs_in_expr shift x || rel_occurs_in_expr shift y
  | BASIC(h,args) -> rel_occurs_in_head shift h || exists_in_expr_list (rel_occurs_in_expr shift) args

let rec rel_occurs_in_type shift (pos,t) = match t with
  | J_Pi(v,t,u) | J_Sigma(v,t,u) -> rel_occurs_in_type shift t || rel_occurs_in_type (shift+1) u
  | J_Singleton(e,t) -> rel_occurs_in_expr shift e || rel_occurs_in_type shift t
  | J_Basic(h,args) -> List.exists (rel_occurs_in_expr shift) args

let rec rel_occurs_in_kind shift = function
  | K_Pi(v,t,k) -> rel_occurs_in_type shift t || rel_occurs_in_kind (shift+1) k
  | K_basic_judgment | K_ulevel | K_syntactic_judgment | K_witnessed_judgment | K_derived_judgment -> false

(** Whether [x] occurs as a name of a free variable in an expression.  Bound variables will get renamed, if in use. *)

let rec occurs_in_head w h =
  match h with
  | V (Var id) -> id_to_name id = w
  | V (Rel _) | W _ | U _ | T _ | O _ | TACTIC _ -> false

and occurs_in_expr w e =
  match unmark e with
  | TEMPLATE(v,body) -> occurs_in_expr w body
  | PAIR(x,y) -> occurs_in_expr w x || occurs_in_expr w y
  | BASIC(h,args) -> occurs_in_head w h || exists_in_expr_list (occurs_in_expr w) args

let rec occurs_in_type w (pos,t) = match t with
  | J_Pi(v,t,u) | J_Sigma(v,t,u) -> occurs_in_type w t || occurs_in_type w u
  | J_Singleton(e,t) -> occurs_in_expr w e || occurs_in_type w t
  | J_Basic(h,args) -> List.exists (occurs_in_expr w) args

let rec occurs_in_kind w = function
  | K_Pi(v,t,k) -> occurs_in_type w t || occurs_in_kind w k
  | K_basic_judgment | K_ulevel | K_syntactic_judgment | K_witnessed_judgment | K_derived_judgment -> false

(** Printing of LF and TS expressions. *)

(*
  Example of pretty printing of variables:

  x |-> ... 0^ ... x ... x0 ...

  Maintain a list of variable substitutions, e.g., [x;x0;...], which means 0^
  prints as x and 1^ prints as x0.  Here x,x0,... are identifiers.

  Replace (relative) references to x by x555 where 555 is the smallest number
  (or empty) so that x555 is not already in the list and also not free or bound
  in the body.

  Then

      x |-> x |-> ... 0^ ... 1^ ... x2 ...

  will print as

      x |-> x1 |-> ... x1 ... x ... x2 ...

 *)

let rel_to_string subs i = try idtostring (List.nth subs i) with Failure "nth" -> vartostring (Rel i)

let var_tester w subs occurs_in e = not ( List.exists (fun x -> id_to_name x == w ) subs ) && not ( occurs_in w e )

let var_chooser x subs rel_occurs_in occurs_in e = 
  if not rel_occurs_in then id "_" :: subs else
  let name = id_to_name x in
  let rec repeat i =
    let name' = if i = -1 then name else name ^ string_of_int i in
    if var_tester name' subs occurs_in e then id name' :: subs
    else repeat (i+1)
  in repeat (-1)

let var_chooser_2 x subs rel_occurs_in occurs_in e =
  let subs = var_chooser x subs rel_occurs_in occurs_in e in
  let x = if enable_variable_prettification then rel_to_string subs 0 else id_to_name x in
  (x,subs)

(* these precedences mirror those in grammar.mly: *)
type associativity = RIGHT | LEFT | NONASSOC
let assoc_to_string = function RIGHT -> "RIGHT" | LEFT -> "LEFT" | NONASSOC -> "NONASSOC"
type precedence = int * associativity
let prec_to_string (i,a) = "(" ^ string_of_int i ^ "," ^ assoc_to_string a ^ ")"
type smart_string = precedence * string
let bottom_prec = 0,NONASSOC
let colon_prec = 10,NONASSOC
let comma_prec = 20,NONASSOC
let binder_prec = 30,RIGHT
let arrow_prec = 40,RIGHT
let times_prec = arrow_prec
let expr_list_prec = 50,LEFT
let star_prec = 60,NONASSOC
let slash_prec = 80,LEFT
let start_prec = 90,NONASSOC
let apply_prec = 100,NONASSOC
let list_prec = 110,LEFT
let top_level = 200
let subscript_prec = top_level,LEFT
let top_prec = top_level,NONASSOC

    (*

       We still need to arrange for all the parentheses in expressions like these:

	   ([ev] f o (_ |-> U))

	   ([ev] f ([ev] g t _) _)

	   _ |-> ([ev] g t _)

       and none here:

	   _ |-> _ |-> T

     *)


type choice = REDUCE | SHIFT | NEITHER

let choose (production:precedence) (token:precedence) =
  (* this algorithm mirrors the behavior of yacc and menhir *)
  let (p,_) = production in
  let (t,a) = token in
  if p > t then REDUCE else
  if p < t then SHIFT else
    match a with
    | RIGHT -> SHIFT
    | LEFT -> REDUCE
    | NONASSOC -> NEITHER

(* to decide whether to parenthesize while printing something like

       a op1 b     op     c op2 d

    where op1,op,op2 have precedences p1,p,p2:

   choose p1 p = SHIFT       (a op1 b)
   choose p1 p = REDUCE       a op1 b
   choose p1 p = NEITHER     (a op1 b)

   choose p p2 = SHIFT        c op2 d
   choose p p2 = REDUCE      (c op2 d)
   choose p p2 = NEITHER     (c op2 d)

*)

let paren_left p (p1,s) = if choose p1 p = REDUCE then s else "(" ^ s ^ ")"

let paren_right p (p2,s) = if choose p p2 = SHIFT then s else "(" ^ s ^ ")"

let paren_always (p,s) = "(" ^ s ^ ")"

let paren_never (p,s) = s

let mark_top s = top_prec, s

let make_top ((i,a),s) = top_prec, if i = top_level then s else "(" ^ s ^ ")"

let rec list_application_to_string p_hd p_arg (head,args) : smart_string =
  List.fold_left
    (fun accu arg -> list_prec, paren_left list_prec accu ^ " " ^ paren_right list_prec (p_arg arg))
    (p_hd head) args

let p1 k = subscript_prec, paren_left subscript_prec k ^ "₁"

let p2 k = subscript_prec, paren_left subscript_prec k ^ "₂"

let application_to_lf_string p_arg head args : smart_string =
  make_top (
  args_fold
    (fun accu arg -> expr_list_prec, paren_left expr_list_prec accu ^ " " ^ paren_right expr_list_prec (p_arg arg))
    p1 p2
    head args)

let rec lf_head_to_string_with_subs subs h : string =
  match h with
  | V (Rel i as v) -> if enable_variable_prettification then rel_to_string subs i else vartostring v
  | V (Var id) -> idtostring id
  | W _ | U _ | T _ | O _ -> "@" ^ expr_head_to_string h
  | TACTIC tac -> tactic_to_string tac

and expr_to_string_with_subs subs e : smart_string =
  match unmark e with
  | TEMPLATE(x,body) ->
      let subs = var_chooser x subs (rel_occurs_in_expr 0 body) occurs_in_expr body in
      let s = expr_to_string_with_subs subs body in
      let x = if enable_variable_prettification then rel_to_string subs 0 else id_to_name x in
      arrow_prec, concat [x;" ⟼ ";paren_right arrow_prec s]
  | PAIR(x,y) ->
      let x = expr_to_string_with_subs subs x in
      let y = expr_to_string_with_subs subs y in
      (* printf " printing pair: prec x = %s, prec y = %s\n\t x = %s\n\t y = %s\n%!" (prec_to_string (fst x)) (prec_to_string (fst y)) (snd x) (snd y); *)
      top_prec, concat ["(pair ";paren_left list_prec x;" ";paren_left list_prec y;")"]
  | BASIC(h,args) ->
      let h = top_prec, lf_head_to_string_with_subs subs h in
      application_to_lf_string (expr_to_string_with_subs subs) h args

and dependent_sub subs prefix infix infix_prec (v,t,u) =
  let used = not enable_variable_prettification || rel_occurs_in_type 0 u in
  let t = judgment_to_string_with_subs subs t in
  let subs = var_chooser v subs (rel_occurs_in_type 0 u) occurs_in_type u in
  let u = judgment_to_string_with_subs subs u in
  let v = if enable_variable_prettification then List.nth subs 0 else v in
  infix_prec,
  (
   if used then
     concat ["("; id_to_name v; ":"; paren_right colon_prec t; ")"]
   else
     paren_left infix_prec t
  )
  ^ infix
  ^ paren_right infix_prec u

and judgment_to_string_with_subs subs (_,t) : smart_string = match t with
  | J_Pi   (v,t,u) -> dependent_sub subs "∏ " " ⟶ " arrow_prec (v,t,u)
  | J_Sigma(v,t,u) -> dependent_sub subs "Σ " " × " times_prec (v,t,u)
  | J_Singleton(x,t) ->
      let x = expr_to_string_with_subs subs x in
      let t = judgment_to_string_with_subs subs t in
      top_prec, concat ["Singleton(";paren_left colon_prec x;" : ";paren_right colon_prec t;")"]
  | J_Basic(hd,args) ->
      list_application_to_string (mark_top <<- judgment_head_to_string) (expr_to_string_with_subs subs) (hd,args)

let rec kind_to_string_with_subs subs = function
  | ( K_ulevel | K_syntactic_judgment | K_derived_judgment | K_basic_judgment | K_witnessed_judgment ) as k -> top_prec, List.assoc k kind_constant_table
  | K_Pi(v,t,k) ->
      let used = rel_occurs_in_kind 0 k in
      let t = judgment_to_string_with_subs subs t in
      let subs = var_chooser v subs (rel_occurs_in_kind 0 k) occurs_in_kind k in
      let infix = " ⟶ " in
      let infix_prec = arrow_prec in
      let k = kind_to_string_with_subs subs k in
      let v = if enable_variable_prettification then rel_to_string subs 0 else id_to_name v in
      if used then
        binder_prec, concat ["(";v; ":"; paren_right colon_prec t; ")";infix; paren_right binder_prec k]
      else
        infix_prec, concat [paren_left infix_prec t; infix; paren_right infix_prec k]

let expr_list_to_string args = paren_left bottom_prec (
  args_fold
    (fun accu arg -> expr_list_prec, paren_left expr_list_prec accu ^ ";" ^ paren_right expr_list_prec (expr_to_string_with_subs [] arg))
    (fun accu -> expr_list_prec, paren_left expr_list_prec accu ^ ";FST")
    (fun accu -> expr_list_prec, paren_left expr_list_prec accu ^ ";SND")
    (top_prec,"") args)

let env_to_subs env = (* concatenation of the two contexts might not be appropriate later on *)
  List.map fst env.local_lf_context
    @  List.map ( fun (name,t) -> id name ) env.local_tts_context

let expr_to_string env e = paren_right bottom_prec (expr_to_string_with_subs (env_to_subs env) e)

let judgment_to_string env t = paren_right bottom_prec (judgment_to_string_with_subs (env_to_subs env) t)

let kind_to_string env k = paren_right bottom_prec (kind_to_string_with_subs (env_to_subs env) k)

(** Printing of TS terms in TS format. *)

let expr_p e = raise NotImplemented

let locate f x =                        (* find the index of the element of the list x for which f is true *)
  let rec repeat i x =
    match x with
    | xi :: x -> if f xi then i else repeat (i+1) x
    | [] -> raise Not_found
  in repeat 0 x

let locations f x =                     (* find the indices of all elements of the list x for which f is true *)
  let rec repeat i x =
    match x with
    | xi :: x -> if f xi then i :: repeat (i+1) x else repeat (i+1) x
    | [] -> []
  in repeat 0 x

let apply n f =                         (* generate f 0 :: f 1 :: f 2 :: ... :: f (n-1) *)
  let rec repeat i =
    if i = n then []
    else f i :: repeat (i+1)
  in repeat 0

let ends_in_paren s = s.[String.length s - 1] = '['

let lf_head_to_string h = lf_head_to_string_with_subs [] h

let possible_comma accu = if (ends_in_paren accu) then accu else accu ^ ","

let rec application_to_ts_string subs hd args = top_prec, (
  args_fold
    (fun accu arg ->
    possible_comma accu ^ paren_right comma_prec (ts_expr_to_string subs arg))
    (fun accu -> possible_comma accu ^ "FST")	(*not right*)
    (fun accu -> possible_comma accu ^ "SND")
    (hd ^ "[")
    args) ^ "]"

and lf_atomic_p subs h args = application_to_ts_string subs (lf_head_to_string_with_subs subs h) args

and ts_expr_to_string subs e : smart_string =
  match unmark e with
  | PAIR(x,y) ->
      let x = ts_expr_to_string subs x in
      let y = ts_expr_to_string subs y in
      top_prec, concat ["(pair ";paren_left list_prec x;" ";paren_left list_prec y;")"] (* does not correspond to our parser *)
  | TEMPLATE(v,body) -> 
      let v,subs = var_chooser_2 v subs (rel_occurs_in_expr 0 body) occurs_in_expr body in
      arrow_prec, (if v = "_" then "" else v) ^ "." ^ paren_right arrow_prec (ts_expr_to_string subs body)
  | BASIC(h,END) -> top_prec, lf_head_to_string_with_subs subs h
  | BASIC(h,args) ->
      match h with
      | T T_Pi -> (
          match args with
          | ARG(t1,ARG((_,TEMPLATE(x,t2)),END)) ->
	      let x,subs' = var_chooser_2 x subs (rel_occurs_in_expr 0 t2) occurs_in_expr t2 in
              top_prec, concat ["@[";expr_head_to_string h;"][";
				paren_left comma_prec (ts_expr_to_string subs t1);",";
				(if x = "_" then "" else x);".";paren_right comma_prec (ts_expr_to_string subs' t2);"]"]
          | _ -> lf_atomic_p subs h args)
      | T T_Sigma -> (
          match args with ARG(t1,ARG((_,TEMPLATE(x, t2)),END)) ->
	    let x,subs' = var_chooser_2 x subs (rel_occurs_in_expr 0 t2) occurs_in_expr t2 in
            top_prec, concat["@[";expr_head_to_string h;"]";"(";
			     paren_left comma_prec (ts_expr_to_string subs t1);",";
			     (if x = "_" then "" else x);".";paren_right comma_prec (ts_expr_to_string subs' t2);
			     ")"]
          | _ -> lf_atomic_p subs h args)
      | O O_ev -> (
          match args with
          | ARG(f,ARG(o,ARG((_,TEMPLATE(x, t)),END))) ->
	      let x,subs' = var_chooser_2 x subs (rel_occurs_in_expr 0 t) occurs_in_expr t in
              top_prec, "[ev;" ^ x ^ "][" ^
	      paren_left comma_prec (ts_expr_to_string subs  f) ^ "," ^
	      paren_left comma_prec (ts_expr_to_string subs  o) ^ "," ^
	      paren_left comma_prec (ts_expr_to_string subs' t) ^ "]"
          | _ -> lf_atomic_p subs h args)
      | O O_lambda -> (
          match args with
          | ARG(t,ARG((_,TEMPLATE(x,o)),END)) ->
	      let x,subs' = var_chooser_2 x subs (rel_occurs_in_expr 0 o) occurs_in_expr o in
              top_prec, "[λ;" (* lambda *) ^ x ^ "][" ^
	      paren_left comma_prec (ts_expr_to_string subs  t) ^ "," ^
	      paren_left comma_prec (ts_expr_to_string subs' o) ^ "]"
          | _ -> lf_atomic_p subs h args)
      | O O_forall -> (
          match args with
          | ARG(u,ARG(u',ARG(o,ARG((_,TEMPLATE(x,o')),END)))) ->
	      let x,subs' = var_chooser_2 x subs (rel_occurs_in_expr 0 o') occurs_in_expr o' in
              top_prec, "[forall;" ^ x ^ "][" ^
              paren_left comma_prec (ts_expr_to_string subs  u ) ^ "," ^
	      paren_left comma_prec (ts_expr_to_string subs  u') ^ "," ^
              paren_left comma_prec (ts_expr_to_string subs  o ) ^ "," ^
	      paren_left comma_prec (ts_expr_to_string subs' o') ^ "]"
          | _ -> lf_atomic_p subs h args)
      | _ -> lf_atomic_p subs h args

(*

(** Printing functions for definitions, provisional. *)

let parmstostring subs = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * expr) list))
    -> concatl [
      if List.length uexp_parms > 0
      then ["(";
            (String.concat " " (List.map (vartostring <<- snd) uexp_parms));
            ":Univ";
            (String.concat "" (List.map
                                 (fun (pos,(u,v)) -> concat ["; ";
							     paren_left bottom_prec (ts_expr_to_string subs u); "=";
							     paren_right bottom_prec (ts_expr_to_string subs v)])
                                 ueqns));
            ")"]
      else [];
      if List.length texp_parms > 0
      then ["(";
            String.concat " " (List.map (vartostring) texp_parms);
            ":Type)"]
      else [];
      List.flatten (List.map
                      (fun (v,t) -> ["(";vartostring v; ":";
				     paren_right colon_prec (ts_expr_to_string subs t);")"])
                      oexp_parms)
    ]

(** Printing of ulevel contexts. *)

let ulevel_context_to_string (UContext(uexp_parms,ueqns)) =
    concatl [
      if List.length uexp_parms > 0
      then [
            (String.concat " " (List.map (vartostring <<- snd) uexp_parms));
            ":Univ";
            (String.concat "" (List.map
                                 (fun (pos,(u,v)) -> concat ["; ";
							     paren_left bottom_prec (ts_expr_to_string subs u); "=";
							     paren_left bottom_prec (ts_expr_to_string subs v)])
                                 ueqns));
            ]
      else [] ]

*)

let ts_expr_to_string env e = paren_left bottom_prec (ts_expr_to_string (env_to_subs env) e)

exception Limit

let rec iteri i f = function
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

let iteri f l = iteri 0 f l

let phantom s = String.make (String.length s) ' '

(** The following routines can be used with [printf "%a"], and are convenient for debugging. *)

let _pos file x = output_string file (errfmt x)

let _i file x = output_string file (idtostring x)

let _im file x = output_string file (idtostring (unmark x))

let _il file x = List.iter (fun x -> printf " "; _i file x) x

let _i_phantom file x = output_string file (phantom (idtostring x))

let _v file x = output_string file (vartostring x)

let _vm file x = output_string file (vartostring (unmark x))

let _vl file x = List.iter (fun x -> printf " "; _v file x) x

let _phantom file x = output_string file (phantom x)

let _v_phantom file x = output_string file (phantom (vartostring x))

let _ts file (env,x) = output_string file (ts_expr_to_string env x)

let _tac file tac = output_string file (tactic_to_string tac)

let _s file x = output_string file (expr_list_to_string x)

let _e file (env,x) = output_string file (expr_to_string env x)

let _el file (env,x) = List.iter (fun x -> printf " "; _e file (env,x)) x

let _a file (env,x) = Array.iter (fun x -> printf " "; _e file (env,x)) x

let _h file x = output_string file (lf_head_to_string x)

let _t file (env,x) = output_string file (judgment_to_string env x)

let _tl file (env,x) = List.iter (fun t -> printf " "; _t file (env,t)) x

let _tn file (env,x) = output_string file (judgment_to_string env (no_pos 123,x))

let _k file (env,x) = output_string file (kind_to_string env x)

let _th file x = output_string file (judgment_head_to_string x)

let _pos_of file x = output_string file (errfmt (get_pos x))

(** Display the signature. *)

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Kind constants:\n";
  List.iter (fun (kind,name) ->
    fprintf file "     %s : kind\n" name
           ) kind_constant_table;
  fprintf file "  Type constants:\n";
  List.iter (fun h ->
    fprintf file "     %a : %a\n" _th h  _k (env,jhead_to_kind h)
           ) judgment_heads;
  fprintf file "  Object constants:\n";
  List.iter (fun h ->
    fprintf file "     %a : %a\n" _h h  _t (env,head_to_type env (Error.no_pos 23) h)
           ) expr_heads;
  flush file

(** Print the context. *)

let print_global_lf_context file env =
  fprintf file "Global LF Context (definitions and axioms):\n";
  MapIdentifier.iter
    (fun name t -> (
      match unmark t with
      | J_Singleton(e,t) ->
          fprintf file "     %a := %a\n"   _i name _e (env,e);
          fprintf file "     %a :  %a\n%!" _i_phantom name _t (env,t)
      | _ ->
          fprintf file "     %a : %a\n%!" _i name _t (env,t)))
    env.global_lf_context

let print_context n file env =
  let n = match n with None -> -1 | Some n -> n in
  fprintf file "LF Context:\n";
  let lfc = List.rev env.local_lf_context in
  let cl = List.length lfc in (
  try iteri
      (fun i (v,t) ->
        if i = n then raise Limit;
        match unmark t with
        | J_Singleton(e,t) ->
            fprintf file " %d %a := %a\n"   (cl-i-1) _i v          _e (env,e);
            fprintf file " %d %a  : %a\n%!" (cl-i-1) _i_phantom v  _t (env,t)
        | _ ->
            fprintf file " %d %a : %a\n%!" (cl-i-1) _i v  _t (env,t)
      )
      lfc
  with Limit -> fprintf file "   ...\n");
  fprintf file "TTS Context:\n";
  let lfc = env.local_tts_context in
  let lfc = if n < 0 then List.rev lfc else lfc in (
  try iteri
      (fun i (name,j) ->
        if i = n then raise Limit;
	match j with
	| TTS_istype -> fprintf file "   %s Type\n%!" name
	| TTS_hastype t -> fprintf file "   %s : %a\n%!" name _e (env,t)
	| TTS_type_equality(t,t') -> fprintf file "   %s : %a == %a\n%!" name _e (env,t) _e (env,t')
	| TTS_object_equality(t,o,o') -> fprintf file "   %s : %a == %a : %a\n%!" name _e (env,o) _e (env,o') _e (env,t)
      )
      lfc
  with Limit -> fprintf file "     ...\n");
  if n = -1 then print_global_lf_context file env

let print_surroundings (surr:surrounding) =
  printf "Surroundings:\n";
  let show_surr (env,i,e,t) =
    (match i with
    | S_projection i -> printf "     projection pi_%d\n" i
    | S_expr_list i -> printf "     argument %d\n" i
    | S_expr_list'(i,h,args_passed,args_coming) -> 
	printf "     argument %d\n        with head %a\n        and with arguments passed: %a\n        and with arguments coming: %a\n" 
	  i _h h _s (reverse_expr_list args_passed) _s (args_coming)
    | S_type_args(i,args_passed) -> 
	printf "     type argument %d\n        with arguments passed: %a\n" i _tl (env,args_passed)
    | S_type_family_args(i,args_passed) ->
	printf "     type family argument %d\n        with arguments passed: %a\n" i _el (env,args_passed)
    | S_body -> printf "     body\n");
    (match e with
    | Some e -> printf "        in expression %a\n" _e (env,e)
    | None -> ());
    (match t with
    | Some t -> printf "        of type %a\n" _t (env,t)
    | None -> ())
  in
  List.iter show_surr surr;
  flush stdout

let prompt env =
  printf "i%d = %!" env.state

(*
  Local Variables:
  compile-command: "make -C .. src/printer.cmo "
  End:
 *)
