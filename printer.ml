(** Functions for converting expressions to strings for printing *)

open Error
open Variables
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

let join a b = List.flatten [a;b]

let pvar free_vars v = if List.mem v free_vars then vartostring v else "_"

(** Lists of free variables. *)

let rec vars_args fv p_arg args = 
  let r = List.map p_arg args in
  join (List.flatten r) fv

let rec atomic_expr_to_free_vars (_,e) = 
  match e with
  | TacticHole n -> []
  | EmptyHole n -> []
  | APPLY(V v,[]) -> [v]
  | APPLY(h,args) -> 
      let fv = match h with V v -> [v] | _ -> [] in
      vars_args fv lf_expr_to_vars args
  | PR1 x
  | PR2 x -> lf_expr_to_vars x

and lf_expr_to_vars = function
  | LAMBDA(x,body) -> remove x (lf_expr_to_vars body)
  | PAIR(_,x,y) -> join (lf_expr_to_vars x) (lf_expr_to_vars y)
  | CAN e -> atomic_expr_to_free_vars e

let rec dependent_vars (v,t,u) = join (lf_type_to_vars t) (remove v (lf_type_to_vars u))

and lf_type_to_vars (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_vars (v,t,u)
  | F_Sigma(v,t,u) -> dependent_vars (v,t,u)
  | F_Singleton(x,t) -> join (lf_expr_to_vars x) (lf_type_to_vars t)
  | F_APPLY(hd,args) -> vars_args [] lf_expr_to_vars args

let rec lf_kind_to_vars = function
  | K_type -> []
  | K_Pi(v,t,k) -> join (lf_type_to_vars t) (remove v (lf_kind_to_vars k))

(** Whether [x] occurs as a free variable in an expression. *)

let rec occurs_in_atomic_expr w (_,e) = 
  match e with
  | TacticHole _ | EmptyHole _ -> false
  | APPLY(V v,args) -> w = v || List.exists (occurs_in_expr w) args
  | APPLY(h,  args) ->          List.exists (occurs_in_expr w) args
  | PR1 e | PR2 e -> occurs_in_expr w e

and occurs_in_expr w = function
  | LAMBDA(v,body) -> w <> v && occurs_in_expr w body
  | PAIR(_,x,y) -> occurs_in_expr w x || occurs_in_expr w y
  | CAN e -> occurs_in_atomic_expr w e

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

let var_sub subs v = try List.assoc v subs with Not_found -> v

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

let rec application_to_string p_hd p_arg (h,args) = 
  let r = List.map p_arg args in
  let args = concat (List.flatten (List.map (fun arg -> [" ";arg]) r)) in
  let s = concat [p_hd h; args] in
  if String.contains s ' ' then concat ["(";s;")"] else s

let rec atomic_expr_to_string_with_subs subs (_,e) = 
  match e with
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ string_of_int n
  | APPLY(V v,[]) -> vartostring (var_sub subs v)
  | APPLY(h,args) -> 
      let h = match h with V v -> V (var_sub subs v) | _ -> h in
      application_to_string lf_expr_head_to_string (lf_expr_to_string_with_subs subs) (h,args)
  | PR1 x -> 
      let s = lf_expr_to_string_with_subs subs x in
      concat ["(π₁ ";s;")"]
  | PR2 x -> 
      let s = lf_expr_to_string_with_subs subs x in
      concat ["(π₂ ";s;")"]

and lf_expr_to_string_with_subs' subs = function (* would be better to implement parsing precedences *)
  | LAMBDA(x,body) -> 
      let w = var_chooser x subs occurs_in_expr body in
      let subs = (x,w) :: subs in
      let s = lf_expr_to_string_with_subs' subs body in
      concat [vartostring w;" ⟼ ";s]
  | _ as e -> lf_expr_to_string_with_subs subs e

and lf_expr_to_string_with_subs subs = function
  | LAMBDA(x,body) -> 
      let w = var_chooser x subs occurs_in_expr body in
      let subs = (x,w) :: subs in
      let s = lf_expr_to_string_with_subs' subs body in
      concat ["(";vartostring (var_sub subs x);" ⟼ ";s;")"]
  | PAIR(_,x,y) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let y = lf_expr_to_string_with_subs subs y in
      concat ["(pair ";x;" ";y;")"]
  | CAN e -> atomic_expr_to_string_with_subs subs e

let rec dependent_sub subs prefix infix target (v,t,u) =
  let used = occurs_in_type v u in
  let w = var_chooser v subs occurs_in_type u in
  let subs = (v,w) :: subs in
  let u = lf_type_to_string_with_subs' true subs u in
  let t = lf_type_to_string_with_subs' used subs t in
  if used then 
    let k = concat ["("; vartostring w; ":"; t; ")"; infix ; u] in
    if target then k else concat ["("; k; ")"]
  else
    let k = concat [t; infix ; u] in
    if target then k else concat ["("; k; ")"]

and lf_type_to_string_with_subs' target subs (_,t) = match t with
  | F_Pi   (v,t,u) -> dependent_sub subs "∏ " " ⟶ " target (v,t,u)
  | F_Sigma(v,t,u) -> dependent_sub subs "Σ " " × " target (v,t,u)
  | F_Singleton(x,t) -> 
      let x = lf_expr_to_string_with_subs subs x in
      let t = lf_type_to_string_with_subs subs t in
      concat ["Singleton(";x;" : ";t;")"]
  | F_APPLY(hd,args) -> 
      application_to_string lf_type_head_to_string (lf_expr_to_string_with_subs subs) (hd,args)

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

let atomic_expr_to_string = atomic_expr_to_string_with_subs []

let lf_type_to_string = lf_type_to_string_with_subs []

let lf_type_to_string' target = lf_type_to_string_with_subs' target []

let lf_kind_to_string = lf_kind_to_string_with_subs []

(** Printing of TS terms in TS format. *)

(** For LF expressions that are not TS terms, print [$$] and then the expression in LF format. *)

let lf_expr_p e = "$$" ^ lf_expr_to_string e

let lf_atomic_p e = "$$" ^ atomic_expr_to_string e

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
    
let rec args_to_string s = String.concat "," (List.map ts_can_to_string s)

and paren_args_to_string s = String.concat "" [ "("; args_to_string s; ")" ]

and ts_can_to_string = function 
  | CAN e -> ts_expr_to_string e
  | PAIR _ | LAMBDA _ as e -> lf_expr_p e		(* normally this branch will not be used *)

and ts_expr_to_string ((_,e) as oe) = 
  (* 
     We assume [oe] is a well typed LF expression of type uexp, texp, or oexp.
     That ensures that the number of branches, the number of lambdas in each branch, and
     the o-t-u identity of each branch is correct.
   *)
  match e with 
  | PR1 _ | PR2 _ -> lf_expr_p (CAN oe)		(* normally this branch will not be used *)
  | TacticHole n -> tactic_to_string n
  | EmptyHole n -> "?" ^ string_of_int n
  | APPLY(V v,[]) -> vartostring v
  | APPLY(h,args) -> (
      let hs = lf_expr_head_to_string h in
      let vardist = head_to_vardist h in (* example: Some (3, [] :: [] :: [0] :: [0;1] :: [0;1;2] :: []) *)
      match vardist with
      | Some(nvars, locs) ->
	  let branches = apply nvars (fun i -> locations (fun x -> List.mem i x) locs) in
	  (* example: branches = [[2;3;4];[3;4];[4]] *)
	  ignore branches;
	  ignore hs
      | _ -> ());
      match h with
      | U uh -> uhead_to_string uh ^ paren_args_to_string args
      | T th -> (
	  match th with 
	  | T_Pi -> (
	      match args with
	      | [CAN t1; LAMBDA( x, CAN t2 )] -> 
		  if false
		  then concat ["(";ts_expr_to_string t1;" ⟶ ";ts_expr_to_string t2;")"]
		  else concat ["[" ^ lf_expr_head_to_string h ^ ";";vartostring x;"](";ts_expr_to_string t1;",";ts_expr_to_string t2;")"]
	      | _ -> lf_atomic_p oe)
	  | T_Sigma -> (
	      match args with [CAN t1; LAMBDA( x, CAN t2 )] -> 
		"[" ^ lf_expr_head_to_string h ^ ";" ^ vartostring x ^ "]" ^
		"(" ^ ts_expr_to_string t1 ^ "," ^ ts_expr_to_string t2 ^ ")"
	      | _ -> lf_atomic_p oe)
	  | T_Coprod2 -> (
	      match args with 
	      | [CAN t; CAN t'; LAMBDA( x,CAN u); LAMBDA( x', CAN u'); CAN o] ->
		  "[" ^ lf_expr_head_to_string h ^ ";" ^ vartostring x ^ "," ^ vartostring x' ^ "](" 
		  ^ ts_expr_to_string t ^ "," ^ ts_expr_to_string t ^ ","
		  ^ ts_expr_to_string u ^ "," ^ ts_expr_to_string u' ^ ","
		  ^ ts_expr_to_string o
		  ^ ")"
	      | _ -> lf_atomic_p oe)
	  | T_IP -> (
	      match args with 
		[CAN tA; CAN a;
		 LAMBDA(x1,CAN tB);
		 LAMBDA(x2,LAMBDA(y2,CAN tD));
		 LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,CAN q)))]
		-> "[" ^ lf_expr_head_to_string h ^ ";" 
		  ^ vartostring x1 ^ ","
		  ^ vartostring x2 ^ "," ^ vartostring y2 ^ "," 
		  ^ vartostring x3 ^ "," ^ vartostring y3 ^ "," ^ vartostring z3 
		  ^ "]("
		  ^ ts_expr_to_string tA ^ "," ^ ts_expr_to_string a ^ "," ^ ts_expr_to_string tB ^ "," ^ ts_expr_to_string tD ^ "," ^ ts_expr_to_string q ^ ")"
	      | _ -> lf_atomic_p oe)
	  | _ -> "[" ^ lf_expr_head_to_string h ^ "]" ^ paren_args_to_string args
	 )
      | O oh -> (
	  match oh with
	  | O_ev -> (
	      match args with 
	      | [CAN f;CAN o;LAMBDA(x, CAN t)] ->
		  "[ev;" ^ vartostring x ^ "](" ^ ts_expr_to_string f ^ "," ^ ts_expr_to_string o ^ "," ^ ts_expr_to_string t ^ ")"
	      | [CAN f;CAN o] ->
		  "[ev;_](" ^ ts_expr_to_string f ^ "," ^ ts_expr_to_string o ^ ")"
	      | _ -> lf_atomic_p oe)
	  | O_lambda -> (
	      match args with 
	      | [CAN t;LAMBDA( x,CAN o)] ->
		  "[λ;" (* lambda *) ^ vartostring x ^ "](" ^ ts_expr_to_string t ^ "," ^ ts_expr_to_string o ^ ")"
	      | _ -> lf_atomic_p oe)
	  | O_forall -> (
	      match args with 
	      | [CAN u;CAN u';CAN o;LAMBDA( x,CAN o')] ->
		  "[forall;" ^ vartostring x ^ "](" ^ ts_expr_to_string u ^ "," ^ ts_expr_to_string u' ^ "," ^ ts_expr_to_string o ^ "," ^ ts_expr_to_string o' ^ ")"
	      | _ -> lf_atomic_p oe)
	  | _ -> "[" ^ ohead_to_string oh ^ "]" ^ paren_args_to_string args
	 )
      | _ -> lf_expr_head_to_string h ^ paren_args_to_string args
(** Printing functions for definitions, provisional. *)

let parmstostring = function
  | ((UContext(uexp_parms,ueqns):uContext),(texp_parms:var list),(oexp_parms:(var * atomic_expr) list)) 
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

(** The following routines can be used with [printf "%a"]. *)

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

