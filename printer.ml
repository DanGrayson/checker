(** Functions for converting expressions to strings for printing *)

open Error
open Typesystem
open Names
open Printf

let space x = " " ^ x
let ( <<- ) f g x = f (g x)
let concat = String.concat ""
let concatl = concat <<- List.flatten

(** Printing of LF expressions. *)

let rec ts_expr_to_string (_,e) = 
  match e with
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ (string_of_int n)
  | APPLY(V v,[]) -> vartostring v
  | APPLY(h,args) -> concat ["(";(lf_expr_head_to_string h);(concat (List.map (space <<- lf_expr_to_string) args));")"]
  | PR1 x -> concat ["(π₁ ";lf_expr_to_string x;")"]
  | PR2 x -> concat ["(π₂ ";lf_expr_to_string x;")"]

and lf_expr_to_string' = function
  | LAMBDA(x,body) -> concat [vartostring x;" ⟼ " (* |-> *) ;lf_expr_to_string' body]
  | _ as e -> lf_expr_to_string e

and lf_expr_to_string = function
  | LAMBDA(x,body) -> concat ["(";vartostring x;" ⟼ ";lf_expr_to_string' body;")"]
  | PAIR(_,x,y) -> concat ["(pair ";lf_expr_to_string x;" ";lf_expr_to_string y;")"]
  | CAN e -> ts_expr_to_string e

let rec lf_type_to_string' target (_,t) = match t with
  | F_Pi(v,t,u) -> 
      if v == VarUnused
      then 
	let k = concat [lf_type_to_string' false t; " ⟶ " (* -> *) ; lf_type_to_string u]
	in if target then k else concat ["("; k; ")"]
      else
	concat ["(∏ " (* Pi *); vartostring v; ":"; lf_type_to_string' false t; ") "; lf_type_to_string u]
  | F_Sigma(v,t,u) -> 
      if v == VarUnused
      then 
	let k = concat [lf_type_to_string' false t; " × " ; lf_type_to_string' false u]
	in if target then k else concat ["("; k; ")"]
      else
	concat ["(Σ " (* Sigma *); vartostring v; ":"; lf_type_to_string' false t; ") "; lf_type_to_string u]
  | F_Singleton(x,t) -> concat ["Singleton(";lf_expr_to_string x;" : ";lf_type_to_string t;")"]
  | F_APPLY(hd,args) -> 
      let s = concat [lf_type_head_to_string hd; concat (List.map (space <<- lf_expr_to_string) args)] in
      if String.contains s ' ' then concat ["(";s;")"] else s
and lf_type_to_string t = lf_type_to_string' true t

let rec lf_kind_to_string = function
  | K_type -> "type"
  | K_Pi(VarUnused,a,k) -> concat [lf_type_to_string' false a;" ⟶ ";lf_kind_to_string k]
  | K_Pi(x,a,k) -> concat ["∏ ";vartostring x;" : ";lf_type_to_string' false a;", ";lf_kind_to_string k]

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)
let lf_expr_p e = "$$" ^ (lf_expr_to_string e)
let lf_atomic_p e = "$$" ^ (ts_expr_to_string e)

let rec args_to_string s = String.concat "," (List.map ts_can_to_string s)
and paren_args_to_string s = String.concat "" [ "("; args_to_string s; ")" ]
and ts_can_to_string = function 
  | CAN e -> ts_expr_to_string e
  | PAIR _ | LAMBDA _ as e -> lf_expr_p e		(* normally this branch will not be used *)
and ts_expr_to_string ((_,e) as oe) = 
  match e with 
  | PR1 _ | PR2 _ -> lf_expr_p (CAN oe)		(* normally this branch will not be used *)
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
	    | [CAN t1; LAMBDA( x, CAN t2 )] -> 
		if x = VarUnused
		then concat ["(";ts_expr_to_string t1;" ⟶ ";ts_expr_to_string t2;")"]
		else concat ["[∏;";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	    | _ -> lf_atomic_p oe)
	| T_Sigma -> (
	    match args with [CAN t1; LAMBDA( x, CAN t2 )] -> "[Sigma;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t1) ^ "," ^ (ts_expr_to_string t2) ^ ")"
	    | _ -> lf_atomic_p oe)
	| T_Coprod2 -> (
	    match args with 
	    | [CAN t; CAN t'; LAMBDA( x,CAN u); LAMBDA( x', CAN u'); CAN o] ->
		"[Coprod;" ^ (vartostring x) ^ "," ^ (vartostring x') ^ "](" 
		^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string t) ^ ","
		^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ ","
		^ (ts_expr_to_string o)
		^ ")"
	    | _ -> lf_atomic_p oe)
	| T_IP -> (
	    match args with 
	      [CAN tA; CAN a;
	       LAMBDA(x1,CAN tB);
	       LAMBDA(x2,LAMBDA(y2,CAN tD));
	       LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,CAN q)))]
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
	    | [CAN f;CAN o;LAMBDA(x, CAN t)] ->
		"[ev;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string t) ^ ")"
	    | [CAN f;CAN o] ->
		"[ev;_](" ^ (ts_expr_to_string f) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_lambda -> (
	    match args with 
	    | [CAN t;LAMBDA( x,CAN o)] ->
		"[λ;" (* lambda *) ^ (vartostring x) ^ "](" ^ (ts_expr_to_string t) ^ "," ^ (ts_expr_to_string o) ^ ")"
	    | _ -> lf_atomic_p oe)
	| O_forall -> (
	    match args with 
	    | [CAN u;CAN u';CAN o;LAMBDA( x,CAN o')] ->
		"[forall;" ^ (vartostring x) ^ "](" ^ (ts_expr_to_string u) ^ "," ^ (ts_expr_to_string u') ^ "," ^ (ts_expr_to_string o) ^ "," ^ (ts_expr_to_string o') ^ ")"
	    | _ -> lf_atomic_p oe)
	| _ -> "[" ^ (ohead_to_string oh) ^ "]" ^ (paren_args_to_string args)
       )
    | _ -> (lf_expr_head_to_string h) ^ (paren_args_to_string args)

(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * atomic_expr) list)) 
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

let p_var file x = output_string file (vartostring x)

let phantom s = String.make (String.length s) ' '

let p_var_phantom file x = output_string file (phantom (vartostring x))

let p_ts file x = output_string file (ts_expr_to_string x)

let p_expr file x = output_string file (lf_expr_to_string x)

let p_expr_head file x = output_string file (lf_expr_head_to_string x)

let p_type file x = output_string file (lf_type_to_string x)

let p_type_head file x = output_string file (lf_type_head_to_string x)

let p_kind file x = output_string file (lf_kind_to_string x)

let p_type_head file x = output_string file (lf_type_head_to_string x)

let p_pos file x = output_string file (errfmt x)

let p_pos_of file x = output_string file (errfmt (get_pos x))

let p_fl file () = flush file

let print_signature env file =
  fprintf file "Signature:\n";
  fprintf file "  Type family constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" p_type_head h  p_kind (tfhead_to_kind h)
	    ) lf_type_heads;
  fprintf file "  Object constants:\n";
  List.iter (fun h -> 
    fprintf file "     %a : %a\n" p_expr_head h  p_type (label_to_type env (Error.no_pos 23) h)
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
	    fprintf file "     %a := %a\n" p_var v          p_expr e;
	    fprintf file "     %a  : %a\n" p_var_phantom v  p_type t; flush file
	| _ -> 
	    fprintf file "     %a : %a\n" p_var v  p_type t; flush file
      ) 
      env
  with Limit -> ()

