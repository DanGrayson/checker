(** Functions for converting expressions to strings for printing *)

open Typesystem

let vartostring' = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | VarUnused -> "_"
let vartostring v = vartostring' (strip_pos_var v)

let uhead_to_string = function
  | U_plus n -> "uplus;" ^ (string_of_int n)
  | U_max -> "max"
let thead_to_string = function
  | T_El -> "El"
  | T_U -> "U"
  | T_Pi -> "Pi"
  | T_Sigma -> "Sigma"
  | T_Pt -> "Pt"
  | T_Coprod -> "Coprod"
  | T_Coprod2 -> "Coprod2"
  | T_Empty -> "Empty"
  | T_IC -> "IC"
  | T_Id -> "Id"
let ohead_to_string = function
  | O_u -> "u"
  | O_j -> "j"
  | O_ev -> "ev"
  | O_lambda -> "lambda"
  | O_forall -> "forall"
  | O_pair -> "pair"
  | O_pr1 -> "pr1"
  | O_pr2 -> "pr2"
  | O_total -> "total"
  | O_pt -> "pt"
  | O_pt_r -> "pt_r"
  | O_tt -> "tt"
  | O_coprod -> "coprod"
  | O_ii1 -> "ii1"
  | O_ii2 -> "ii2"
  | O_sum -> "sum"
  | O_empty -> "empty"
  | O_empty_r -> "empty_r"
  | O_c -> "c"
  | O_ic_r -> "ic_r"
  | O_ic -> "ic"
  | O_paths -> "paths"
  | O_refl -> "refl"
  | O_J -> "J"
  | O_rr0 -> "rr0"
  | O_rr1 -> "rr1"
let head_to_string = function
  | Defapp (name,i) -> "[defapp;" ^ name ^ "," ^ (string_of_int i) ^ "]"
  | U h -> "[" ^ uhead_to_string h ^ "]"
  | T h -> "[" ^ thead_to_string h ^ "]"
  | O h -> "[" ^ ohead_to_string h ^ "]"

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
	| _ -> (head_to_string h) ^ (parenelisttostring args)
       )
and elisttostring s = String.concat "," (List.map ts_expr_to_string s)
and parenelisttostring s = String.concat "" [ "("; elisttostring s; ")" ]

let tfhead_to_string = function
  | F_uexp -> "Uexp"
  | F_texp -> "Texp"
  | F_oexp -> "Oexp"
  | F_Is_type -> "Istype"
  | F_Has_type -> "Hastype"
  | F_Type_equality -> "TEquality"
  | F_Object_equality -> "OEquality"

let parens x = "(" ^ x ^ ")"
let space x = " " ^ x
let (<<-) f g x = f (g x)
let concat = String.concat ""
let concatl x = concat (List.flatten x)

let rec lf_type_family_to_string = function
  | F_Hole -> "_"
  | F_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- ts_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
  | F_Pi(v,t,u) -> concat ["Pi "; vartostring' v; ":"; (lf_type_family_to_string t); ", "; lf_type_family_to_string u]

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

let rec lfl label s = "(" ^ label ^ (String.concat "" (List.map (fun x -> " " ^ (lftostring x)) s)) ^ ")"
and lftostring = function
  | LAMBDA(x,body) -> "(LAMBDA " ^ (vartostring x) ^ " : Obj, " ^ (lftostring body) ^ ")"
  | POS(_,e) -> match e with 
    | EmptyHole n -> "_" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> lfl (head_to_string h) args

