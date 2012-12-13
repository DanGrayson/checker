(** Functions for converting expressions to strings for printing *)

open Error
open Variables
open Helpers
open Typesystem
open Names
open Printf

let space x = " " ^ x

let ( <<- ) f g x = f (g x)

let concat = String.concat ""

let concatl = concat <<- List.flatten

let rec remove x = function
  | [] -> []
  | y :: rest -> if x = y then remove x rest else y :: remove x rest

let pvar free_vars v = if List.mem v free_vars then vartostring v else "_"

(** Lists of free variables. *)

let rec vars_arglist p_arg args = List.flatten (List.map p_arg args)

let rec vars_args p_arg args = 
  match args with 
  | ARG(x,args) -> p_arg x @ vars_args p_arg args
  | CAR args | CDR args -> vars_args p_arg args
  | END -> []

let rec lf_expr_to_vars (pos,e) = match e with
  | LAMBDA(x,body) -> remove x (lf_expr_to_vars body)
  | APPLY(f,t,x) -> lf_expr_to_vars f @ lf_type_to_vars t @ lf_expr_to_vars x
  | CONS(x,y) -> lf_expr_to_vars x @ lf_expr_to_vars y
  | EVAL(V v,END) -> [v]
  | EVAL(h,args) -> 
      let fv = match h with V v -> [v] | _ -> [] in
      fv @ vars_args lf_expr_to_vars args

and dependent_vars (v,t,u) = lf_type_to_vars t @ remove v (lf_type_to_vars u)

and lf_type_to_vars (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_vars (v,t,u)
  | F_Sigma(v,t,u) -> dependent_vars (v,t,u)
  | F_Singleton(x,t) -> lf_expr_to_vars x @ lf_type_to_vars t
  | F_APPLY(hd,args) -> vars_arglist lf_expr_to_vars args

let rec lf_kind_to_vars = function
  | K_type -> []
  | K_Pi(v,t,k) -> lf_type_to_vars t @ remove v (lf_kind_to_vars k)

(** Whether [x] occurs as a free variable in an expression. *)

let rec occurs_in_expr w e = 
  match unmark e with 
  | APPLY(f,t,x) -> occurs_in_expr w f || occurs_in_type w t || occurs_in_expr w x
  | LAMBDA(v,body) -> w <> v && occurs_in_expr w body
  | CONS(x,y) -> occurs_in_expr w x || occurs_in_expr w y
  | EVAL(V v,args) -> w = v || arg_exists (occurs_in_expr w) args
  | EVAL(h,  args) ->          arg_exists (occurs_in_expr w) args

and occurs_in_type w (_,t) = match t with
  | F_Pi   (v,t,u)
  | F_Sigma(v,t,u) -> occurs_in_type w t || w <> v && occurs_in_type w u
  | F_Singleton(e,t) -> occurs_in_expr w e || occurs_in_type w t
  | F_APPLY(hd,args) -> List.exists (occurs_in_expr w) args

let rec occurs_in_kind w = function
  | K_type -> false
  | K_Pi(v,t,k) -> occurs_in_type w t || w <> v && occurs_in_kind w k

(** Printing of LF and TS expressions. 

    In the names of the following routines, "fvs" refers to "free variables and strings".
*)

(*
  Example of pretty printing:

  x$111 |-> ... x$111 ... x$222 ... x2 ...

  Can't make it pretty in one pass

  Maintain a list of variable substitutions, e.g., x$222 => x, x$333 => x0, ...

  Refer to the list whenever printing a variable

  Replace x$111 by x555 where 555 is the smallest number (or empty) so that x555 is not in the target of the list
  and also not free in the body

  Then  

      x$222 |-> x$111 |-> ... x$111 ... x$222 ... x2 ...

  will print as

      x |-> x1 |-> ... x1 ... x ... x2 ...

 *)

let enable_variable_prettification = true

let var_sub subs v = 
  if enable_variable_prettification && (not !debug_mode)
  then (try List.assoc v subs with Not_found -> v) 
  else v

let var_tester w subs occurs_in e =
  not( List.exists (fun (_,v) -> v = w) subs )
    &&
  not( occurs_in w e )

let var_chooser x subs occurs_in e =
  match x with
  | VarGen(i,name) as v -> 
      if not (occurs_in v e) then Var "_" else
      let w = Var name in
      if var_tester w subs occurs_in e then w
      else let rec repeat i =
	let w = Var (name ^ string_of_int i) in
	if var_tester w subs occurs_in e then w
	else repeat (i+1)
      in repeat 0
  | _ -> x

let occurs_in_list occurs_in x args = List.exists (occurs_in x) args

let rec spine_application_to_string p_hd p_arg (h,args) = 
  args_fold
    (fun accu arg -> accu ^ " " ^ p_arg arg)
    (fun accu -> "(π₁ " ^ accu ^ ")")
    (fun accu -> "(π₂ " ^ accu ^ ")")
    (p_hd h)
    args

let target_paren target k = if target || (not (String.contains k ' ')) then k else "(" ^ k ^ ")"

let rec list_application_to_string p_hd p_arg (h,args) = 
  List.fold_left
    (fun accu arg -> accu ^ " " ^ p_arg arg)
    (p_hd h)
    args

let rec lf_expr_to_string_with_subs' subs e =   (* would be better to implement parsing precedences *)
  match unmark e with
  | LAMBDA(x,body) -> 
      let w = var_chooser x subs occurs_in_expr body in
      let subs = (x,w) :: subs in
      let s = lf_expr_to_string_with_subs' subs body in
      concat [vartostring w;" ⟼ ";s]
  | _  -> lf_expr_to_string_with_subs subs e

and lf_expr_to_string_with_subs subs e = 
  match unmark e with
  | LAMBDA(x,body) -> 
      let w = var_chooser x subs occurs_in_expr body in
      let subs = (x,w) :: subs in
      let s = lf_expr_to_string_with_subs' subs body in
      concat ["(";vartostring (var_sub subs x);" ⟼ ";s;")"]
  | CONS(x,y) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let y = lf_expr_to_string_with_subs subs y in
      concat ["(pair ";x;" ";y;")"]
  | APPLY(f,t,x) -> 
      let f = lf_expr_to_string_with_subs subs f in
      let t = lf_type_to_string_with_subs subs t in
      let x = lf_expr_to_string_with_subs subs x in
      concat ["((";f;" : ";t;") ";x;")"]
  | EVAL(V v,END) -> vartostring (var_sub subs v)
  | EVAL(h,args) -> 
      let h = match h with V v -> V (var_sub subs v) | _ -> h in
      "(" ^ (spine_application_to_string lf_expr_head_to_string (lf_expr_to_string_with_subs subs) (h,args)) ^ ")"

and dependent_sub subs prefix infix target (v,t,u) =
  let used = occurs_in_type v u in
  let w = var_chooser v subs occurs_in_type u in
  let subs = (v,w) :: subs in
  let u = lf_type_to_string_with_subs' true subs u in
  let t = lf_type_to_string_with_subs' used subs t in
  let k = (
    if used then 
      concat ["("; vartostring w; ":"; t; ")"; infix ; u]
    else
      concat [t; infix ; u]) in
  target_paren target k

and lf_type_to_string_with_subs' target subs (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_sub subs "∏ " " ⟶ " target (v,t,u)
  | F_Sigma(v,t,u) -> dependent_sub subs "Σ " " × " target (v,t,u)
  | F_Singleton(x,t) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let t = lf_type_to_string_with_subs subs t in
      concat ["Singleton(";x;" : ";t;")"]
  | F_APPLY(hd,args) -> 
      let k = list_application_to_string lf_type_head_to_string (lf_expr_to_string_with_subs subs) (hd,args) in
      target_paren target k

and lf_type_to_string_with_subs subs t = lf_type_to_string_with_subs' true subs t

let rec lf_kind_to_string_with_subs subs = function
  | K_type -> "type"
  | K_Pi(v,t,k) -> 
      let used = occurs_in_kind v k in
      let w = var_chooser v subs occurs_in_kind k in
      let subs = (v,w) :: subs in
      let prefix = "∏ " in
      let infix = " ⟶ " in
      let t = lf_type_to_string_with_subs' false subs t in
      let k = lf_kind_to_string_with_subs subs k in
      if used then
	concat ["(";prefix; vartostring v; ":"; t; ") "; k]
      else
	concat [t; infix; k]

let lf_expr_to_string = lf_expr_to_string_with_subs []

let lf_type_to_string = lf_type_to_string_with_subs []

let lf_type_to_string' target = lf_type_to_string_with_subs' target []

let lf_kind_to_string = lf_kind_to_string_with_subs []

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)

let lf_expr_p e = "$$" ^ lf_expr_to_string e

let lf_atomic_p e = "$$" ^ lf_expr_to_string e

let locate f x = 			(* find the index of the element of the list x for which f is true *)
  let rec repeat i x =
    match x with 
    | xi :: x -> if f xi then i else repeat (i+1) x
    | [] -> raise Not_found
  in repeat 0 x

let locations f x = 			(* find the indices of all elements of the list x for which f is true *)
  let rec repeat i x =
    match x with 
    | xi :: x -> if f xi then i :: repeat (i+1) x else repeat (i+1) x
    | [] -> []
  in repeat 0 x

let apply n f =				(* generate f 0 :: f 1 :: f 2 :: ... :: f (n-1) *)
  let rec repeat i =
    if i = n then []
    else f i :: repeat (i+1)
  in repeat 0
    
let ends_in_paren s = s.[String.length s - 1] = '('

let rec paren_args_to_string hd args = (
  args_fold
    (fun accu arg -> 
      (if (ends_in_paren accu) then accu else accu ^ ",") ^ ts_expr_to_string arg)
    (fun accu -> "[π₁](" ^ accu ^ ")")
    (fun accu -> "[π₂](" ^ accu ^ ")")
    (hd ^ "(")
    args) ^ ")"

and ts_expr_to_string e = 
  (* 
     We assume [oe] is a well typed LF expression of type uexp, texp, or oexp.
     That ensures that the number of branches, the number of lambdas in each branch, and
     the o-t-u identity of each branch is correct.
   *)
  match unmark e with 
  | APPLY _ | CONS _ | LAMBDA _ -> lf_expr_p e		(* normally this branch will not be used *)
  | EVAL(V v,END) -> vartostring v
  | EVAL(h,args) -> 
      match h with
      | T T_Pi -> (
	  match args with
	  | ARG(t1,ARG((_,LAMBDA(x, t2)),END)) -> 
	      if false
	      then concat ["(";ts_expr_to_string t1;" ⟶ ";ts_expr_to_string t2;")"]
	      else concat ["[" ^ lf_expr_head_to_string h ^ ";";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	  | _ -> lf_atomic_p e)
      | T T_Sigma -> (
	  match args with ARG(t1,ARG((_,LAMBDA(x, t2)),END)) -> 
	    "[" ^ lf_expr_head_to_string h ^ ";" ^ vartostring x ^ "]" ^
	    "(" ^ ts_expr_to_string t1 ^ "," ^ ts_expr_to_string t2 ^ ")"
	  | _ -> lf_atomic_p e)
      | O O_ev -> (
	  match args with 
	  | ARG(f,ARG(o,ARG((_,LAMBDA(x, t)),END))) ->
	      "[ev;" ^ vartostring x ^ "](" ^ ts_expr_to_string f ^ "," ^ ts_expr_to_string o ^ "," ^ ts_expr_to_string t ^ ")"
	  | ARG(f,ARG(o,END)) ->
	      "[ev;_](" ^ ts_expr_to_string f ^ "," ^ ts_expr_to_string o ^ ")"
	  | _ -> lf_atomic_p e)
      | O O_lambda -> (
	  match args with 
	  | ARG(t,ARG((_,LAMBDA(x,o)),END)) ->
	      "[λ;" (* lambda *) ^ vartostring x ^ "](" ^ ts_expr_to_string t ^ "," ^ ts_expr_to_string o ^ ")"
	  | _ -> lf_atomic_p e)
      | O O_forall -> (
	  match args with 
	  | ARG(u,ARG(u',ARG(o,ARG((_,LAMBDA(x,o')),END)))) ->
	      "[forall;" ^ vartostring x ^ "](" ^ 
	      ts_expr_to_string u ^ "," ^ ts_expr_to_string u' ^ "," ^ 
	      ts_expr_to_string o ^ "," ^ ts_expr_to_string o' ^ ")"
	  | _ -> lf_atomic_p e)
      | _ -> paren_args_to_string (lf_expr_head_to_string h) args

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * lf_expr) list)) 
    -> concatl [
      if List.length uexp_parms > 0 
      then ["(";
	    (String.concat " " (List.map (vartostring) uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ")"]
      else [];
      if List.length texp_parms > 0
      then ["("; 
	    String.concat " " (List.map (vartostring) texp_parms);
	    ":Type)"]
      else [];
      List.flatten (List.map 
		      (fun (v,t) -> ["(";vartostring v; ":"; ts_expr_to_string t;")"])
		      oexp_parms)
    ]

(** Printing of ulevel contexts. *)

let ulevel_context_to_string (UContext(uexp_parms,ueqns)) = 
    concatl [
      if List.length uexp_parms > 0 
      then [
	    (String.concat " " (List.map (vartostring) uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ]
      else [] ]

exception Limit

let rec iteri i f = function
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

let iteri f l = iteri 0 f l

let phantom s = String.make (String.length s) ' '

(** The following routines can be used with [printf "%a"]. *)

let _v file x = output_string file (vartostring x)

let _v_phantom file x = output_string file (phantom (vartostring x))

let _ts file x = output_string file (ts_expr_to_string x)

let _e file x = output_string file (lf_expr_to_string x)

let _eh file x = output_string file (lf_expr_head_to_string x)

let _t file x = output_string file (lf_type_to_string x)

let _th file x = output_string file (lf_type_head_to_string x)

let _k file x = output_string file (lf_kind_to_string x)

let _th file x = output_string file (lf_type_head_to_string x)

let _pos file x = output_string file (errfmt x)

let _pos_of file x = output_string file (errfmt (get_pos x))

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Type family constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" _th h  _k (tfhead_to_kind h)
	   ) lf_type_heads;
  fprintf file "  Object constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" _eh h  _t (label_to_type env (Error.no_pos 23) h)
	   ) lf_expr_heads;
  flush file

let print_context n file (env:context) = 
  let n = match n with None -> -1 | Some n -> n in
  fprintf file "Context:\n";
  try iteri
      (fun i (v,t) ->
	if i = n then raise Limit;
	match unmark t with
	| F_Singleton(e,t) ->
	    fprintf file "     %a := %a\n" _v v          _e e;
	    fprintf file "     %a  : %a\n" _v_phantom v  _t t; flush file
	| _ -> 
	    fprintf file "     %a : %a\n" _v v  _t t; flush file
     ) 
      env
  with Limit -> ()

