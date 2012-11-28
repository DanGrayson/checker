(** A template for complete matching against expressions. *)

open Typesystem

let template = function
  | LAMBDA(x,body) -> ()
  | POS(pos,e) -> match e with
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
		| [t1; LAMBDA( x, t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Sigma -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Pt -> ()
	    | T_Coprod -> ()
	    | T_Coprod2 -> (
		match args with
		| [t;t'; LAMBDA(x,u);LAMBDA( x', u');o] -> ()
		| _ -> raise Error.Internal)
	    | T_Empty -> ()
	    | T_IC -> (
		match args with
		| [tA;a;LAMBDA(x1,tB);LAMBDA(x2,LAMBDA(y2,tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,q)))] -> ()
		| _ -> raise Error.Internal)
	    | T_Id -> (
		match args with
		| [tX; x; x'] -> ()
		| _ -> raise Error.Internal)
	   )
	| O oh -> (
	    match oh with
	    | O_u -> ()
	    | O_j -> ()
	    | O_ev -> (
		match args with
		| [f;o;LAMBDA( x,t)] -> ()
		| [f;o] -> ()
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with
		| [t;LAMBDA( x,o)] -> ()
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with
		| [u;u';o;LAMBDA( x,o')] -> ()
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
	    | O_ic_r -> ()
	    | O_ic -> ()
	    | O_paths -> ()
	    | O_refl -> ()
	    | O_J -> ()
	    | O_rr0 -> ()
	    | O_rr1 -> ()
	   )
	| _ -> raise Error.NotImplemented
       )
