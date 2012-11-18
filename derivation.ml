(** Judgments, inference rules, and derivations. *)

open Typesystem

(** We introduce the various types of judgment. *)

type j_c = unit
	(**{v Gamma |> v}*)

type j_t = tExpr
	(**{v Gamma |- T type v}*)
	(* 
	   TS doesn't mention this one, so in this implementation we will consider
	   [ Gamma |- T type ] and [ Gamma, x:T |> ] to be alpha equivalent, for compatibility with TS 
	 *)

type j_o = oExpr * tExpr
	(**{v Gamma |- o : T v}*)

type j_teq = tExpr * tExpr
	(**{v Gamma |- T = T' v}*)

type j_oeq = oExpr * oExpr * tExpr
	(**{v Gamma |- o = o' : T v}*)

type judgmentBody =
  | J_c of j_c
  | J_t of j_t
  | J_o of j_o
  | J_teq of j_teq
  | J_oeq of j_oeq

type judgment = oContext * judgmentBody

(** We introduce the various types of derivation, corresponding to the various type of judgment. *)
type derivation = {
    d_uc : utContext;
    d_rule : rule_application }
and rule_application =
  | R_t_append of r_t_append
  | R_fetch of r_fetch
  | R_empty of r_empty
  | R_ev of r_ev
  | R_teq_symm of r_teq_symm
  | R_teq_trans of r_teq_trans
  | R_oeq_symm of r_oeq_symm
  | R_oeq_trans of r_oeq_trans
  | R_o_cast of r_o_cast
  | R_oeq_cast of r_oeq_cast
  | R_u_append of r_u_append
(* templates
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
*)
and r_empty = {
    r_empty_judgment : j_c; 
  }
      (**{v
 	 ---------------------------------  empty (rule 4)
 	       Gamma |>
	 v}*)
and r_t_append = {
    r_t_append_name : string;
    r_t_append_d : derivation;
    r_t_append_judgment : j_t; 
  }
      (**{v
	 d  :: G |- 
 	 ---------------------------------  t_append X (rule 5)
 	       G |- X type
	 v}*)
and r_fetch = {
    r_fetch_name : string;
    r_fetch_d : derivation;
    r_fetch_judgment : j_o; 
  }
      (**{v
	 d  :: G,x:X,G' |- 
 	 ---------------------------------  fetch x (rule 6)
 	       G,x:X,G' |- x:X
	 v}*)
and r_teq_symm = {
    r_teq_symm_d : derivation;
    r_teq_symm_judgment : j_teq; 
  }
      (**{v
	 d  :: G |- T = T'
 	 --------------------------------- teq_symm (rule 8)
 	       G |- T' = T
	 v}*)
and r_teq_trans = {
    r_teq_trans_12 : derivation; 
    r_teq_trans_23 : derivation;
    r_teq_trans_judgment : j_teq; 
  }
      (**{v
	 12 :: G |- T1 T2
	 23 :: G |- T2 T3
 	 --------------------------------- teq_trans (rule 9)
 	       G |- T1 T3
	 v}*)
and r_oeq_symm = {
    r_oeq_symm_d : derivation;
    r_oeq_symm_judgment : j_oeq; 
  }
      (**{v
	 d  :: G |- o1 = o2 : T
 	 --------------------------------- oeq_symm (rule 11)
 	       G |- o2 = o1 : T
	 v}*)
and r_oeq_trans = {
    r_oeq_trans_12 : derivation;
    r_oeq_trans_23 : derivation;
    r_oeq_trans_judgment : j_oeq; 
  }
      (**{v
	 12 :: G |- o1 = o2 : T
	 23 :: G |- o2 = o3 : T
 	 --------------------------------- oeq_trans (rule 12)
 	       G |- o1 = o3 : T
	 v}*)
and r_o_cast = { 
    r_o_cast_o : derivation; 
    r_o_cast_teq : derivation;
    r_o_cast_judgment : j_o; 
  }
      (**{v
 	 o  :: G |- o : T
	 tt :: G |- T = T'
 	 --------------------------------- o_cast (rule 13)
 	       G |- o : T'
	 v}*)
and r_oeq_cast = {
    r_oeq_cast_oeq : derivation; 
    r_oeq_cast_teq : derivation;
    r_oeq_cast_judgment : j_oeq; 
  }
      (**{v
 	 oo :: G |- o = o' : T
	 tt :: G |- T = T'
 	 --------------------------------- oeq_cast (rule 14)
	       G |- o = o' : T'
	 v}*)
and r_u_append = {
    r_u_append_d : derivation; 
    r_u_append_M : uExpr;
    r_u_append_judgment : j_t; 
  }
      (**{v
	 d :: G |>
	 M :: Ulevel
 	 --------------------------------- u_append (rule 15)
 	      G |- [U](M) type
	 v}*)
and r_u_type = {
    r_u_type_d : derivation; 
    r_u_type_M : uExpr;
    r_u_type_judgment : j_o; 
  }
      (**{v
	 d :: G |>
	 M :: Ulevel
 	 --------------------------------- u_type (rule 15)
 	      G |- [u](M) : [U](M+1)
	 v}*)








and r_ev = { 
    r_ev_f  : derivation; 
    r_ev_o  : derivation;
    r_ev_teq : derivation; 		(* it was a suggestion of Andrej Bauer to add this prerequisite *)
    r_ev_judgment : j_o; 
  }
      (**{v
	 f  :: G |- f : Pi x:T, U
	 o  :: G |- o : T'
	 tt :: G |- T = T'
	 ------------------------------------------ ev (rule 25)
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

(* TEMPLATE
and r_ = {
    r__ : derivation; 
    r__judgment : j_; 
  }
      (**{v
	  :: G |- 
 	 ---------------------------------  (rule )
 	       G |- 
	 v}*)
*)
