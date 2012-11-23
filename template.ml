(** A template for complete matching against expressions. *)

open Typesystem

let template = function
  | LAMBDA(x,bodies) -> ()
  | POS(pos,e) -> match e with
    | EmptyHole -> ()
    | Variable t -> ()
    | APPLY(h,args) -> (
	match h with
	| Defapp _ -> ()
	| UU uh -> (
	    match uh with 
	    | UU_plus n -> ()
	    | UU_max -> ()
	   )
	| TT th -> (
	    match th with 
	    | TT_El -> ()
	    | TT_U -> ()
	    | TT_Pi -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> ()
		| _ -> raise Error.Internal)
	    | TT_Sigma -> (
		match args with
		| [t1; LAMBDA( x, t2 )] -> ()
		| _ -> raise Error.Internal)
	    | TT_Pt -> ()
	    | TT_Coprod -> ()
	    | TT_Coprod2 -> (
		match args with
		| [t;t'; LAMBDA(x,u);LAMBDA( x', u');o] -> ()
		| _ -> raise Error.Internal)
	    | TT_Empty -> ()
	    | TT_IC -> (
		match args with
		| [tA;a;LAMBDA(x1,tB);LAMBDA(x2,LAMBDA(y2,tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,q)))] -> ()
		| _ -> raise Error.Internal)
	    | TT_Id -> (
		match args with
		| [tX; x; x'] -> ()
		| _ -> raise Error.Internal)
	   )
	| OO oh -> (
	    match oh with
	    | OO_u -> ()
	    | OO_j -> ()
	    | OO_ev -> (
		match args with
		| [f;o;LAMBDA( x,t)] -> ()
		| [f;o] -> ()
		| _ -> raise Error.Internal)
	    | OO_lambda -> (
		match args with
		| [t;LAMBDA( x,o)] -> ()
		| _ -> raise Error.Internal)
	    | OO_forall -> (
		match args with
		| [u;u';o;LAMBDA( x,o')] -> ()
		| _ -> raise Error.Internal)
	    | OO_pair -> ()
	    | OO_pr1 -> ()
	    | OO_pr2 -> ()
	    | OO_total -> ()
	    | OO_pt -> ()
	    | OO_pt_r -> ()
	    | OO_tt -> ()
	    | OO_coprod -> ()
	    | OO_ii1 -> ()
	    | OO_ii2 -> ()
	    | OO_sum -> ()
	    | OO_empty -> ()
	    | OO_empty_r -> ()
	    | OO_c -> ()
	    | OO_ic_r -> ()
	    | OO_ic -> ()
	    | OO_paths -> ()
	    | OO_refl -> ()
	    | OO_J -> ()
	    | OO_rr0 -> ()
	    | OO_rr1 -> ()
	   )
       )
