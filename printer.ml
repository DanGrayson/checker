(** Functions for converting expressions to strings for printing *)

open Typesystem
open Names
open Printf

let space x = " " ^ x
let ( <<- ) f g x = f (g x)
let concat = String.concat ""
let concatl = concat <<- List.flatten

(** Printing of LF expressions. *)

let rec lf_atomic_to_string (_,e) = 
  match e with
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ (string_of_int n)
  | APPLY(V v,[]) -> vartostring v
  | APPLY(h,args) -> concat ["(";(label_to_string h);(concat (List.map (space <<- lf_expr_to_string) args));")"]
and lf_expr_to_string' = function
  | LAMBDA(x,body) -> concat [vartostring x;" ⟼ " (* |-> *) ;lf_expr_to_string' body]
  | Phi e -> lf_atomic_to_string e
and lf_expr_to_string = function
  | LAMBDA(x,body) -> concat ["(";vartostring x;" ⟼ ";lf_expr_to_string' body;")"]
  | Phi e -> lf_atomic_to_string e

let rec lf_type_to_string' target (_,t) = match t with
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then 
	let k = concat [lf_type_to_string' false t; " ⟶ " (* -> *) ; lf_type_to_string u]
	in if target then k else concat ["("; k; ")"]
      else
	concat ["∏ " (* Pi *); vartostring v; ":"; lf_type_to_string' false t; ", "; lf_type_to_string u]
  | F_Singleton(x,t) -> concat ["Singleton(";lf_expr_to_string x;" : ";lf_type_to_string t;")"]
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- lf_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
and lf_type_to_string t = lf_type_to_string' true t

let rec lf_kind_to_string = function
  | K_type -> "type"
  | K_Pi(VarUnused,a,k) -> concat [lf_type_to_string' false a;" ⟶ ";lf_kind_to_string k]
  | K_Pi(x,a,k) -> concat ["∏ ";vartostring x;" : ";lf_type_to_string' false a;", ";lf_kind_to_string k]

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)
let lf_expr_p e = "$$" ^ (lf_expr_to_string e)
let lf_atomic_p e = "$$" ^ (lf_atomic_to_string e)

let rec args_to_string s = String.concat "," (List.map ts_can_to_string s)
and paren_args_to_string s = String.concat "" [ "("; args_to_string s; ")" ]
and ts_can_to_string = function 
  | Phi e -> ts_expr_to_string e
  | LAMBDA _ as e -> lf_expr_p e		(* normally this branch will not be used *)
and ts_expr_to_string ((_,e) as oe) = match e with 
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ (string_of_int n)
  | APPLY(V v,[]) -> vartostring v
  | APPLY(h,args) -> 
    match h with
    | U uh -> (uhead_to_string uh) ^ (paren_args_to_string args)
    | T th -> (
	match th with 
	| T_Pi -> (
	    match args with
	    | [Phi t1; LAMBDA( x, Phi t2 )] -> 
		if x = VarUnused
		then concat ["(";ts_expr_to_string t1;" ⟶ ";ts_expr_to_string t2;")"]
		else concat ["[∏;";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	    | _ -> lf_atomic_p oe)
	| T_Sigma -> (
	    match args with [Phi t1; LAMBDA( x, Phi t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
	    | _ -> lf_atomic_p oe)
	| T_Coprod2 -> (
	    match args with 
	    | [Phi t; Phi t'; LAMBDA( x,Phi u); LAMBDA( x', Phi u'); Phi o] ->
		"[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		^ (ts_expr_to_string o)
		^ ")"
	    | _ -> lf_atomic_p oe)
	| T_IP -> (
	    match args with 
	      [Phi tA; Phi a;
	       LAMBDA(x1,Phi tB);
	       LAMBDA(x2,LAMBDA(y2,Phi tD));
	       LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,Phi q)))]
	      -> "[IP;" 
		^ (vartostring x1) ^ ","
		^ (vartostring x2) ^ "," ^ (vartostring y2) ^ "," 
		^ (vartostring x3) ^ "," ^ (vartostring y3) ^ "," ^ (vartostring z3) 
		^ "]("
		^ (ts_expr_to_string tA) ^ "," ^ (ts_expr_to_string a) ^ "," ^ (ts_expr_to_string tB) ^ "," ^ (ts_expr_to_string tD) ^ "," ^ (ts_expr_to_string q) ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (thead_to_string th) ^ "]" ^ (paren_args_to_string args)
       )
    | O oh -> (
	match oh with
	| O_ev -> (
	    match args with 
	    | [Phi f;Phi o;LAMBDA(x, Phi t)] ->
		"[ev;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
	    | [Phi f;Phi o] ->
		"[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_lambda -> (
	    match args with 
	    | [Phi t;LAMBDA( x,Phi o)] ->
		"[λ;" (* lambda *) ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_forall -> (
	    match args with 
	    | [Phi u;Phi u';Phi o;LAMBDA( x,Phi o')] ->
		"[forall;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (paren_args_to_string args)
       )
    | _ -> (label_to_string h) ^ (paren_args_to_string args)

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * ts_expr) list)) 
    -> concatl [
      if List.length uexp_parms > 0 
      then ["(";
	    (String.concat " " (List.map vartostring uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ")"]
      else [];
      if List.length texp_parms > 0
      then ["("; 
	    String.concat " " (List.map vartostring texp_parms);
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
	    (String.concat " " (List.map vartostring uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ]
      else [] ]

(** Printing of an environment. *)

exception Limit

let rec iteri i f = function
    [] -> ()
  | a::l -> f i a; iteri (i + 1) f l

let iteri f l = iteri 0 f l

let print_context n file env = 
  let n = match n with  None -> -1 | Some n -> n in
  fprintf file "Context:\n";
  try
    iteri
      (fun i (v,t) ->
	if i = n then raise Limit;
	fprintf file "     %s : %s\n" (vartostring v) (lf_type_to_string t);
	flush file) 
      env
    with Limit -> ();
  flush file

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Type family constants:\n";
  List.iter (fun h -> fprintf file "     %s : %s\n" (tfhead_to_string h) (lf_kind_to_string (tfhead_to_kind h))) tfheads;
  fprintf file "  Object constants:\n";
  List.iter (fun h -> fprintf file "     %s : %s\n" (label_to_string h) (lf_type_to_string (label_to_type env (Error.no_pos 23) h))) labels;
  flush file
