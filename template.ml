(** A template for complete matching against expressions. *)

open Typesystem

let template = function
  | LAMBDA(x,body) -> ()
  | CAN(pos,e) -> match e with
    | EmptyHole _ -> ()
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
		| [CAN t1; LAMBDA( x, CAN t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Sigma -> (
		match args with
		| [CAN t1; LAMBDA( x, CAN t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Pt -> ()
	    | T_Coprod -> ()
	    | T_Coprod2 -> (
		match args with
		| [CAN t;CAN t'; LAMBDA(x,CAN u);LAMBDA( x', CAN u'); CAN o] -> ()
		| _ -> raise Error.Internal)
	    | T_Empty -> ()
	    | T_IP -> (
		match args with
		| [CAN tA;CAN a;LAMBDA(x1,CAN tB);LAMBDA(x2,LAMBDA(y2,CAN tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,CAN q)))] -> ()
		| _ -> raise Error.Internal)
	    | T_Id -> (
		match args with
		| [CAN tX; CAN x; CAN x'] -> ()
		| _ -> raise Error.Internal)
	   )
	| O oh -> (
	    match oh with
	    | O_u -> ()
	    | O_j -> ()
	    | O_ev -> (
		match args with
		| [CAN f; CAN o;LAMBDA( x,CAN t)] -> ()
		| [CAN f; CAN o] -> ()
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with
		| [CAN t;LAMBDA( x,CAN o)] -> ()
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with
		| [CAN u;CAN u';CAN o;LAMBDA( x,CAN o')] -> ()
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
