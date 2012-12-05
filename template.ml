(** A template for complete matching against expressions. *)

open Typesystem

let template = function
  | LAMBDA(x,body) -> ()
  | Phi(pos,e) -> match e with
    | TacticHole _ -> ()
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
		| [Phi t1; LAMBDA( x, Phi t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Sigma -> (
		match args with
		| [Phi t1; LAMBDA( x, Phi t2 )] -> ()
		| _ -> raise Error.Internal)
	    | T_Pt -> ()
	    | T_Coprod -> ()
	    | T_Coprod2 -> (
		match args with
		| [Phi t;Phi t'; LAMBDA(x,Phi u);LAMBDA( x', Phi u'); Phi o] -> ()
		| _ -> raise Error.Internal)
	    | T_Empty -> ()
	    | T_IP -> (
		match args with
		| [Phi tA;Phi a;LAMBDA(x1,Phi tB);LAMBDA(x2,LAMBDA(y2,Phi tD));LAMBDA(x3,LAMBDA(y3,LAMBDA(z3,Phi q)))] -> ()
		| _ -> raise Error.Internal)
	    | T_Id -> (
		match args with
		| [Phi tX; Phi x; Phi x'] -> ()
		| _ -> raise Error.Internal)
	   )
	| O oh -> (
	    match oh with
	    | O_u -> ()
	    | O_j -> ()
	    | O_ev -> (
		match args with
		| [Phi f; Phi o;LAMBDA( x,Phi t)] -> ()
		| [Phi f; Phi o] -> ()
		| _ -> raise Error.Internal)
	    | O_lambda -> (
		match args with
		| [Phi t;LAMBDA( x,Phi o)] -> ()
		| _ -> raise Error.Internal)
	    | O_forall -> (
		match args with
		| [Phi u;Phi u';Phi o;LAMBDA( x,Phi o')] -> ()
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
