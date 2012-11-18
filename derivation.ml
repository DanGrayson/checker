(** Judgments, inference rules, and derivations. *)

open Typesystem

type judgementBody =
  | J_c
	(**{v Gamma |> v}*)
  | J_t of tExpr
	(**{v Gamma |- T type v}*)
	(* 
	   TS doesn't mention this one, so in this implementation we will consider
	   [ Gamma |- T type ] and [ Gamma, x:T |> ] to be alpha equivalent, for compatibility with TS 
	 *)
  | J_o of oExpr * tExpr
	(**{v Gamma |- o : T v}*)
  | J_tt of tExpr * tExpr
	(**{v Gamma |- T = T' v}*)
  | J_oo of oExpr * oExpr * tExpr
	(**{v Gamma |- o = o' : T v}*)
type judgement = oContext * judgementBody
type derivation = {
    d_uc : utContext;
    d_judg : judgement;
    d_rule : rule_application }
and rule_application =
  | R_append of r_append
  | R_empty of r_empty
  | R_tcast of r_tcast
  | R_ev of r_ev
and r_empty = unit
      (**{v
 	 ---------------------------------  empty (rule 4)
 	       Gamma |>
	 v}*)
and r_append = {
    r_append_name : string;
    r_append_d : derivation
  }
      (**{v
	 d  :: Gamma |- 
 	 ---------------------------------  append (rule 5)
 	       Gamma |- X type
	 v}*)
and r_tcast = { 
    r_tcast_ot : derivation; 
    r_tcast_tt : derivation }
      (**{v
 	 ot :: Gamma |- o : T
	 tt :: Gamma |- T = T'
 	 --------------------------------- tcast (rule 13)
 	       Gamma |- o : T'
	 v}*)
and r_ev = { 
    r_ev_f  : derivation; 
    r_ev_o  : derivation;
    r_ev_tt : derivation 		(* it was a suggestion of Andrej Bauer to add this prerequisite *)
  }
      (**{v
	 f  :: Gamma |- f : Pi x:T, U
	 o  :: Gamma |- o : T'
	 tt :: Gamma |- T = T'
	 ------------------------------------------ ev (rule 25)
	       Gamma |- [ev;x](f,o,U) : U[o/x]
v}*)


(*   Rule tetaempty :: Pi {Gamma : MContext} (T T' : MType),		# eta reduction for empty
		     Pi j :: Gamma |- a : Empty,
		     Gamma |- T = T'.

   Rule oetaempty :: Pi {Gamma : MContext} {T : MType} {a o o' : MObject},		# eta reduction for empty
		     Pi j :: Gamma |- a : Empty,
		     Pi k :: o : T,
		     Pi k' :: o' : T,
		     Gamma |- o = o' : T.
*)

(* TEMPLATE
and r_ = {
    r_ : derivation; 
    r_ : derivation
  }
      (**{v
	  :: Gamma |- 
 	 ---------------------------------  (rule )
 	       Gamma |- 
	 v}*)
*)
