(** Functions for converting expressions to strings for printing *)

open Typesystem

let parens x = "(" ^ x ^ ")"
let space x = " " ^ x
let (<<-) f g x = f (g x)
let concat = String.concat ""
let concatl x = concat (List.flatten x)

let rec ts_expr_to_string = function
  | LAMBDA(x,body) -> "LAMBDA " ^ (vartostring x) ^ ", " ^ (ts_expr_to_string body)
  | POS(_,e) -> match e with 
    | EmptyHole n -> "?" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> (
	match h with
	| U uh -> (
	    match uh with 
	    | U_plus n -> (
		match args with 
		| [u] -> "(" ^ (ts_expr_to_string u) ^ "+" ^ (string_of_int n) ^ ")"
		| _ -> raise Error.Internal
	       )
	    | _ -> (uhead_to_string uh) ^ (parenelisttostring args)
	    )
	| T th -> (
	    match th with 
	    | T_Pi -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> "[Pi;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> raise Error.Internal)
	    | T_Sigma -> (
		match args with [t1; LAMBDA( x, t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> raise Error.Internal)
	    | T_Coprod2 -> (
		match args with 
		| [t;t'; LAMBDA( x,u);LAMBDA( x', u');o] ->
		    "[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		    ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		    ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		    ^ (ts_expr_to_string o)
		    ^ ")"
		| _ -> raise Error.Internal)
	    | T_IC -> (
		match args with 
		  [tA;a;LAMBDA(x1,tB);LAMBDA(x2,LAMBDA(y2,tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,q)))]
		  -> "[IC;" 
		    ^ (vartostring x1) ^ ","
		    ^ (vartostring x2) ^ "," ^ (vartostring y2) ^ "," 
		    ^ (vartostring x3) ^ "," ^ (vartostring y3) ^ "," ^ (vartostring z3) 
		    ^ "]("
		    ^ (ts_expr_to_string tA) ^ "," ^ (ts_expr_to_string a) ^ "," ^ (ts_expr_to_string tB) ^ "," ^ (ts_expr_to_string tD) ^ "," ^ (ts_expr_to_string q) ^ ")"
		| _ -> raise Error.Internal)
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
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with 
		| [t;LAMBDA( x,o)] ->
		    "[lambda;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with 
		| [u;u';o;LAMBDA( x,o')] ->
		    "[forall;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
		| _ -> raise Error.Internal)
	    | _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (parenelisttostring args)
	   )
	| _ -> concat ["["; (label_to_string h); "]"; (parenelisttostring args)]
       )
and elisttostring s = String.concat "," (List.map ts_expr_to_string s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]

let rec lf_type_family_to_string = function
  | F_hole -> "_"
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- ts_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then concat ["("; (lf_type_family_to_string t); " -> "; lf_type_family_to_string u; ")"]
      else concat ["PI "; vartostring' v; ":"; (lf_type_family_to_string t); ", "; lf_type_family_to_string u]

let ueqntostring (u,v) = concat ["; "; ts_expr_to_string u; "="; ts_expr_to_string v]

let octostring (v,t) = concat [vartostring' v; ":"; ts_expr_to_string t]

let parmstostring = function
  | ((UContext(uvars,ueqns):uContext),(tc:tContext),(oc:oContext)) 
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

let rec lfl label s = "(" ^ label ^ (String.concat "" (List.map (fun x -> " " ^ (lf_expr_to_string x)) s)) ^ ")"
and lf_expr_to_string = function
  | LAMBDA(x,body) -> "(LAMBDA " ^ (vartostring x) ^ ", " ^ (lf_expr_to_string body) ^ ")"
  | POS(_,e) -> match e with 
    | EmptyHole n -> "_" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> lfl (label_to_string h) args

