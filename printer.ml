(** Functions for converting expressions to strings for printing *)

open Typesystem

let space x = " " ^ x
let ( <<- ) f g x = f (g x)
let concat = String.concat ""

(** Printing of LF expressions. *)

let rec lf_expr_to_string = function
  | LAMBDA(x,body) -> "(lambda " ^ (vartostring x) ^ ", " ^ (lf_expr_to_string body) ^ ")"
  | POS(_,e) -> match e with 
    | EmptyHole n -> "_" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> " $(" ^ (label_to_string h) ^ (String.concat "" (List.map (fun x -> " " ^ (lf_expr_to_string x)) args)) ^ ")"

let rec lftype_to_string = function
  | F_hole -> "_"
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- lf_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then concat ["("; lftype_to_string t; " -> "; lftype_to_string u; ")"]
      else concat ["Pi "; vartostring' v; ":"; lftype_to_string t; ", "; lftype_to_string u]

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)
let lfp e = "$$" ^ (lf_expr_to_string e)

let rec elisttostring s = String.concat "," (List.map ts_expr_to_string s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]
and ts_expr_to_string = function
  | POS(_,e) as oe -> (match e with 
    | EmptyHole n -> "?" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> (
	match h with
	| U uh -> (
	    match uh with 
	    | U_plus n -> (
		match args with 
		| [u] -> "(" ^ (ts_expr_to_string u) ^ "+" ^ (string_of_int n) ^ ")"
		| _ -> lfp oe
	       )
	    | _ -> (uhead_to_string uh) ^ (parenelisttostring args)
	    )
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
	| _ -> concat ["["; (label_to_string h); "]"; (parenelisttostring args)]
       ))
  | oe -> lfp oe

(** Printing functions for definitions, provisional. *)

let ueqntostring (u,v) = concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]

let octostring (v,t) = concat [vartostring' v; ":"; ts_expr_to_string t]

let parmstostring = function
  | ((UContext(uvars,ueqns):uContext),(tc:var' list),(oc:ts_context)) 
    -> (
      if List.length uvars > 0 
      then "(" ^ (String.concat " " (List.map vartostring' uvars)) ^ ":Univ" ^ (String.concat "" (List.map ueqntostring ueqns)) ^ ")"
      else "" )
      ^ 
	(
	 if List.length tc > 0
	 then "(" ^ (String.concat " " (List.map vartostring' tc)) ^ ":Type)"
	 else ""
	) ^
      (String.concat "" (List.map (fun x -> "(" ^ (octostring x) ^ ")") oc))
