(** Functions for converting expressions to strings for printing *)

open Typesystem

let space x = " " ^ x
let ( <<- ) f g x = f (g x)
let concat = String.concat ""
let concatl = concat <<- List.flatten

(** Printing of LF expressions. *)

let rec lfexpr_to_string = function
  | LAMBDA(x,body) -> "(lambda " ^ (vartostring x) ^ ", " ^ (lfexpr_to_string body) ^ ")"
  | POS(_,e) -> match e with 
    | EmptyHole n -> "_" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> "(" ^ (label_to_string h) ^ (String.concat "" (List.map (fun x -> " " ^ (lfexpr_to_string x)) args)) ^ ")"

let rec lftype_to_string target = function
  | F_hole -> "_"
  | F_Singleton(x,t) -> concat ["= ";lfexpr_to_string x;" : ";lftype_to_string true t;""]
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- lfexpr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then 
	let k = concat [lftype_to_string false t; " -> "; lftype_to_string true u]
	in if target then k else concat ["("; k; ")"]
      else
	concat ["Pi "; vartostring' v; ":"; lftype_to_string false t; ", "; lftype_to_string true u]

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)
let lfp e = "$$" ^ (lfexpr_to_string e)

let rec elisttostring s = String.concat "," (List.map ts_expr_to_string s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]
and ts_expr_to_string = function
  | POS(_,e) as oe -> (match e with 
    | EmptyHole n -> "?" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> (
	match h with
	| U uh -> (uhead_to_string uh) ^ (parenelisttostring args)
	| T th -> (
	    match th with 
	    | T_Pi -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> "[Pi;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> lfp oe)
	    | T_Sigma -> (
		match args with [t1; LAMBDA( x, t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> lfp oe)
	    | T_Coprod2 -> (
		match args with 
		| [t;t'; LAMBDA( x,u);LAMBDA( x', u');o] ->
		    "[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		    ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		    ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		    ^ (ts_expr_to_string o)
		    ^ ")"
		| _ -> lfp oe)
	    | T_IC -> (
		match args with 
		  [tA;a;LAMBDA(x1,tB);LAMBDA(x2,LAMBDA(y2,tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,q)))]
		  -> "[IC;" 
		    ^ (vartostring x1) ^ ","
		    ^ (vartostring x2) ^ "," ^ (vartostring y2) ^ "," 
		    ^ (vartostring x3) ^ "," ^ (vartostring y3) ^ "," ^ (vartostring z3) 
		    ^ "]("
		    ^ (ts_expr_to_string tA) ^ "," ^ (ts_expr_to_string a) ^ "," ^ (ts_expr_to_string tB) ^ "," ^ (ts_expr_to_string tD) ^ "," ^ (ts_expr_to_string q) ^ ")"
		| _ -> lfp oe)
	    | _ -> "[" ^ (thead_to_string th) ^ "]" ^ (parenelisttostring args)
	   )
	| O oh -> (
	    match oh with
	    | O_ev -> (
		match args with 
		| [f;o;LAMBDA( x,t)] ->
		    "[ev;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
		| [f;o] ->
		    "[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
		| _ -> lfp oe)
	    | O_lambda -> (
		match args with 
		| [t;LAMBDA( x,o)] ->
		    "[lambda;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
		| _ -> lfp oe)
	    | O_forall -> (
		match args with 
		| [u;u';o;LAMBDA( x,o')] ->
		    "[forall;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
		| _ -> lfp oe)
	    | _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (parenelisttostring args)
	   )
	| _ -> (label_to_string h) ^ (parenelisttostring args)
       ))
  | oe -> lfp oe

(** Printing functions for definitions, provisional. *)
let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var' list),(oexp_parms:(var' * expr) list)) 
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

