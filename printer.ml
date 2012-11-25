(** Functions for converting expressions to strings for printing *)

open Typesystem

let vartostring' = function
  | Var x -> x
  | VarGen(i,x) -> x ^ "_" ^ (string_of_int i)
  | VarUnused -> "_"
let vartostring v = vartostring' (strip_pos_var v)

let uhead_to_string = function
  | UU_plus n -> "uplus;" ^ (string_of_int n)
  | UU_max -> "max"
let thead_to_string = function
  | TT_El -> "El"
  | TT_U -> "U"
  | TT_Pi -> "Pi"
  | TT_Sigma -> "Sigma"
  | TT_Pt -> "Pt"
  | TT_Coprod -> "Coprod"
  | TT_Coprod2 -> "Coprod2"
  | TT_Empty -> "Empty"
  | TT_IC -> "IC"
  | TT_Id -> "Id"
let ohead_to_string = function
  | OO_u -> "u"
  | OO_j -> "j"
  | OO_ev -> "ev"
  | OO_lambda -> "lambda"
  | OO_forall -> "forall"
  | OO_pair -> "pair"
  | OO_pr1 -> "pr1"
  | OO_pr2 -> "pr2"
  | OO_total -> "total"
  | OO_pt -> "pt"
  | OO_pt_r -> "pt_r"
  | OO_tt -> "tt"
  | OO_coprod -> "coprod"
  | OO_ii1 -> "ii1"
  | OO_ii2 -> "ii2"
  | OO_sum -> "sum"
  | OO_empty -> "empty"
  | OO_empty_r -> "empty_r"
  | OO_c -> "c"
  | OO_ic_r -> "ic_r"
  | OO_ic -> "ic"
  | OO_paths -> "paths"
  | OO_refl -> "refl"
  | OO_J -> "J"
  | OO_rr0 -> "rr0"
  | OO_rr1 -> "rr1"
let head_to_string = function
  | Defapp (name,i) -> "[defapp;" ^ name ^ "," ^ (string_of_int i) ^ "]"
  | UU h -> "[" ^ uhead_to_string h ^ "]"
  | TT h -> "[" ^ thead_to_string h ^ "]"
  | OO h -> "[" ^ ohead_to_string h ^ "]"

let rec ts_expr_to_string = function
  | LAMBDA(x,body) -> "LAMBDA " ^ (vartostring x) ^ ", " ^ (ts_expr_to_string body)
  | POS(_,e) -> match e with 
    | EmptyHole n -> "?" ^ (string_of_int n)
    | Variable v -> vartostring' v
    | APPLY(h,args) -> (
	match h with
	| UU uh -> (
	    match uh with 
	    | UU_plus n -> (
		match args with 
		| [u] -> "(" ^ (ts_expr_to_string u) ^ "+" ^ (string_of_int n) ^ ")"
		| _ -> raise Error.Internal
	       )
	    | _ -> (uhead_to_string uh) ^ (parenelisttostring args)
	    )
	| TT th -> (
	    match th with 
	    | TT_Pi -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> "[Pi;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> raise Error.Internal)
	    | TT_Sigma -> (
		match args with [t1; LAMBDA( x, t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
		| _ -> raise Error.Internal)
	    | TT_Coprod2 -> (
		match args with 
		| [t;t'; LAMBDA( x,u);LAMBDA( x', u');o] ->
		    "[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		    ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		    ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		    ^ (ts_expr_to_string o)
		    ^ ")"
		| _ -> raise Error.Internal)
	    | TT_IC -> (
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
	| OO oh -> (
	    match oh with
	    | OO_ev -> (
		match args with 
		| [f;o;LAMBDA( x,t)] ->
		    "[ev;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
		| [f;o] ->
		    "[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
		| _ -> raise Error.Internal)
	    | OO_lambda -> (
		match args with 
		| [t;LAMBDA( x,o)] ->
		    "[lambda;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
		| _ -> raise Error.Internal)
	    | OO_forall -> (
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
  | TF_Uexpr -> "Uexpr"
  | TF_Texpr -> "Texpr"
  | TF_Oexpr -> "Oexpr"
  | TF_Is_type -> "Istype"
  | TF_Has_type -> "Hastype"
  | TF_Type_equality -> "TEquality"
  | TF_Object_equality -> "OEquality"

let parens x = "(" ^ x ^ ")"
let space x = " " ^ x
let (<<-) f g x = f (g x)
let concat = String.concat ""
let concatl x = concat (List.flatten x)

let rec lf_type_family_to_string = function
  | TF_Hole -> "_"
  | TF_APPLY(hd,args) -> 
      let s = concat [tfhead_to_string hd; concat (List.map (space <<- ts_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
  | TF_Pi(v,t,u) -> concat ["Pi "; vartostring' v; ":"; (lf_type_family_to_string t); ", "; lf_type_family_to_string u]

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

