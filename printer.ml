(** Functions for converting expressions to strings for printing *)

open Typesystem

let space x = " " ^ x
let ( <<- ) f g x = f (g x)
let concat = String.concat ""
let concatl = concat <<- List.flatten

(** Printing of LF expressions. *)

let rec lf_atomic_to_string (_,e) = match e with
  | EmptyHole n -> "?" ^ (string_of_int n)
  | Variable v -> vartostring' v
  | APPLY(h,args) -> concat ["(";(label_to_string h);(concat (List.map (space <<- lf_canonical_to_string) args));")"]
and lf_canonical_to_string = function
  | LAMBDA(x,body) -> concat ["(lambda ";vartostring x;", ";lf_canonical_to_string body;")"]
  | ATOMIC e -> lf_atomic_to_string e

let rec lf_type_to_string' target (_,t) = match t with
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then 
	let k = concat [lf_type_to_string' false t; " -> "; lf_type_to_string u]
	in if target then k else concat ["("; k; ")"]
      else
	concat ["Pi "; vartostring' v; ":"; lf_type_to_string' false t; ", "; lf_type_to_string u]
  | F_Singleton(x,t) -> concat ["= ";lf_canonical_to_string x;" : ";lf_type_to_string t;""]
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- lf_canonical_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
and lf_type_to_string t = lf_type_to_string' true t

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)
let lf_canonical_p e = "$$" ^ (lf_canonical_to_string e)
let lf_atomic_p e = "$$" ^ (lf_atomic_to_string e)

let rec args_to_string s = String.concat "," (List.map ts_can_to_string s)
and paren_args_to_string s = String.concat "" [ "("; args_to_string s; ")" ]
and ts_can_to_string = function 
  | ATOMIC e -> ts_expr_to_string e
  | LAMBDA _ as e -> lf_canonical_p e		(* normally this branch will not be used *)
and ts_expr_to_string ((_,e) as oe) = match e with 
  | EmptyHole n -> "?" ^ (string_of_int n)
  | Variable v -> vartostring' v
  | APPLY(h,args) -> 
    match h with
    | U uh -> (uhead_to_string uh) ^ (paren_args_to_string args)
    | T th -> (
	match th with 
	| T_Pi -> (
	    match args with
	    | [ATOMIC t1; LAMBDA( x, ATOMIC t2 )] -> 
		if unmark x = VarUnused
		then concat ["(";ts_expr_to_string t1;"->";ts_expr_to_string t2;")"]
		else concat ["[Pi;";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	    | _ -> lf_atomic_p oe)
	| T_Sigma -> (
	    match args with [ATOMIC t1; LAMBDA( x, ATOMIC t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
	    | _ -> lf_atomic_p oe)
	| T_Coprod2 -> (
	    match args with 
	    | [ATOMIC t; ATOMIC t'; LAMBDA( x,ATOMIC u); LAMBDA( x', ATOMIC u'); ATOMIC o] ->
		"[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		^ (ts_expr_to_string o)
		^ ")"
	    | _ -> lf_atomic_p oe)
	| T_IP -> (
	    match args with 
	      [ATOMIC tA; ATOMIC a;
	       LAMBDA(x1,ATOMIC tB);
	       LAMBDA(x2,LAMBDA(y2,ATOMIC tD));
	       LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,ATOMIC q)))]
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
	    | [ATOMIC f;ATOMIC o;LAMBDA(x, ATOMIC t)] ->
		"[ev;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
	    | [ATOMIC f;ATOMIC o] ->
		"[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_lambda -> (
	    match args with 
	    | [ATOMIC t;LAMBDA( x,ATOMIC o)] ->
		"[lambda;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_forall -> (
	    match args with 
	    | [ATOMIC u;ATOMIC u';ATOMIC o;LAMBDA( x,ATOMIC o')] ->
		"[forall;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (paren_args_to_string args)
       )
    | _ -> (label_to_string h) ^ (paren_args_to_string args)

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var' list),(oexp_parms:(var' * ts_expr) list)) 
    -> concatl [
      if List.length uexp_parms > 0 
      then ["(";
	    (String.concat " " (List.map vartostring' uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ")"]
      else [];
      if List.length texp_parms > 0
      then ["("; 
	    String.concat " " (List.map vartostring' texp_parms);
	    ":Type)"]
      else [];
      List.flatten (List.map 
		      (fun (v,t) -> ["(";vartostring' v; ":"; ts_expr_to_string t;")"])
		      oexp_parms)
    ]

(** Printing of ulevel contexts. *)

let ulevel_context_to_string (UContext(uexp_parms,ueqns)) = 
    concatl [
      if List.length uexp_parms > 0 
      then [
	    (String.concat " " (List.map vartostring' uexp_parms));
	    ":Univ";
	    (String.concat "" (List.map 
				 (fun (u,v) -> concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]) 
				 ueqns));
	    ]
      else [] ]

(** Printing of an environment. *)
let print_env env = 
  Printf.printf "Environment :\n";
  List.iter 
    (fun (v,t) -> Printf.printf "   %s : %s\n" (vartostring' v) (lf_type_to_string t)) 
    (List.rev env);
  flush stdout
