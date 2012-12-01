(** A template for complete matching against expressions. *)

open Typesystem

let template = function
  | LAMBDA(x,body) -> ()
  | ATOMIC(pos,e) -> match e with
    | EmptyHole _ -> ()
    | Variable t -> ()
    | APPLY(h,args) -> (
	match h with
	| U uh -> (
	    match uh with 
	    | U_next -> ()
	    | U_max -> ()
	   )
	| T th -> (
	    match th with 
	    | T_El -> ()
	    | T_U -> ()
	    | T_Pi -> (
		match args with
		| [ATOMIC t1; LAMBDA( x, ATOMIC t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Sigma -> (
		match args with
		| [ATOMIC t1; LAMBDA( x, ATOMIC t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Pt -> ()
	    | T_Coprod -> ()
	    | T_Coprod2 -> (
		match args with
		| [ATOMIC t;ATOMIC t'; LAMBDA(x,ATOMIC u);LAMBDA( x', ATOMIC u'); ATOMIC o] -> ()
		| _ -> raise Error.Internal)
	    | T_Empty -> ()
	    | T_IP -> (
		match args with
		| [ATOMIC tA;ATOMIC a;LAMBDA(x1,ATOMIC tB);LAMBDA(x2,LAMBDA(y2,ATOMIC tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,ATOMIC q)))] -> ()
		| _ -> raise Error.Internal)
	    | T_Id -> (
		match args with
		| [ATOMIC tX; ATOMIC x; ATOMIC x'] -> ()
		| _ -> raise Error.Internal)
	   )
	| O oh -> (
	    match oh with
	    | O_u -> ()
	    | O_j -> ()
	    | O_ev -> (
		match args with
		| [ATOMIC f; ATOMIC o;LAMBDA( x,ATOMIC t)] -> ()
		| [ATOMIC f; ATOMIC o] -> ()
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with
		| [ATOMIC t;LAMBDA( x,ATOMIC o)] -> ()
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with
		| [ATOMIC u;ATOMIC u';ATOMIC o;LAMBDA( x,ATOMIC o')] -> ()
		| _ -> raise Error.Internal)
	    | O_pair -> ()
	    | O_pr1 -> ()
	    | O_pr2 -> ()
	    | O_total -> ()
	    | O_pt -> ()
	    | O_pt_r -> ()
	    | O_tt -> ()
	    | O_coprod -> ()
	    | O_ii1 -> ()
	    | O_ii2 -> ()
	    | O_sum -> ()
	    | O_empty -> ()
	    | O_empty_r -> ()
	    | O_c -> ()
	    | O_ip_r -> ()
	    | O_ip -> ()
	    | O_paths -> ()
	    | O_refl -> ()
	    | O_J -> ()
	    | O_rr0 -> ()
	    | O_rr1 -> ()
	   )
	| _ -> raise Error.NotImplemented
       )
