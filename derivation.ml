(** Judgments, inference rules, and derivations. *)

open Typesystem


type judgementBody =
  | J_c
	(**{v Gamma |> v}*)
  | J_t of tExpr
	(**{v Gamma |- T type  v}*)
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
  | R_tcast of r_tcast
  | R_ev of r_ev
and r_tcast = { 
    r_tcast_ot : derivation; 
    r_tcast_tt : derivation }
      (**{v
 	 ot :: G |- o : T
	 tt :: G |- T = T'
 	 --------------------------------- tcast (rule 13)
 	 G |- o : T'
	 v}*)
and r_ev = { 
    r_ev_f  : derivation; 
    r_ev_o  : derivation;
    r_ev_tt : derivation }
      (**{v
	 f  :: G |- f : Pi x:T, U
	 o  :: G |- o : T'
	 tt :: G |- T = T'
	 --------------------------------- ev (rule 25)
	 G |- [ev;x](f,o,U) : U[o/x]
v}*)


(*   Rule tetaempty :: Pi {G : MContext} (T T' : MType),		# eta reduction for empty
		     Pi j :: G |- a : Empty,
		     G |- T = T'.

   Rule oetaempty :: Pi {G : MContext} {T : MType} {a o o' : MObject},		# eta reduction for empty
		     Pi j :: G |- a : Empty,
		     Pi k :: o : T,
		     Pi k' :: o' : T,
		     G |- o = o' : T.
*)
