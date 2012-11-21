(** Judgments, inference rules, and derivations. *)

open Typesystem

(** We introduce the various types of judgment. *)

type j_c = unit
	(**{v Gamma |> v}*)

type j_t = expr
	(**{v Gamma |- T type v}*)
	(* 
	   TS doesn't mention this one, so in this implementation we will consider
	   [ Gamma |- T type ] and [ Gamma, x:T |> ] to be alpha equivalent, for compatibility with TS 
	 *)

type j_o = expr * expr
	(**{v Gamma |- o : T v}*)

type j_teq = expr * expr
	(**{v Gamma |- T = T' v}*)

type j_oeq = expr * expr * expr
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
    d_judgment : judgment;
    d_justification : rule_application
  }
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
  | R_u_type of r_u_type
  | R_el_u of r_el_u
  | R_el_u_red of r_el_u_red
  | R_el_u_eq of r_el_u_eq
(* templates
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
  | R_ of r_
*)
and r_empty = unit
      (**{v
 	 ---------------------------------  empty (rule 4)
 	       |>
	 v}*)
and r_t_append = {
    r_t_append_name : string;
    r_t_append_d : derivation;
  }
      (**{v
	 d  :: G |> 
 	 ---------------------------------  t_append X, for X in FV (rule 5)
 	       G |- X type
	 v}*)
and r_fetch = {
    r_fetch_i : int;
    r_fetch_d : derivation;
  }
      (**{v
	 d  :: G,x:X,G' |> 
 	 ---------------------------------  fetch i, where i is the length of G' (rule 6)
 	       G,x:X,G' |- x:X
	 v}*)
and r_teq_refl = {
    r_teq_refl_t1 : derivation; 
    r_teq_refl_t2 : derivation; 
  }
      (**{v
	 t1 :: G |- T1 type
	            T1 ~ T2
	 t2 :: G |- T2 type
 	 --------------------------------- teq_refl (rule 7)
 	       G |- T1 = T2
	 v}*)
and r_teq_symm = {
    r_teq_symm_d : derivation;
  }
      (**{v
	 d  :: G |- T = T'
 	 --------------------------------- teq_symm (rule 8)
 	       G |- T' = T
	 v}*)
and r_teq_trans = {
    r_teq_trans_12 : derivation; 
    r_teq_trans_teq : derivation; 		(* it was a suggestion of Andrej Bauer to add this prerequisite *)
    r_teq_trans_23 : derivation;
  }
      (**{v
	 12 :: G |- T1 = T2
	 teq:: G |- T2 = T2'
	 23 :: G |- T2' = T3

 	 --------------------------------- teq_trans (rule 9)
 	       G |- T1 = T3
	 v}*)
and r_oeq_refl = {
    r_oeq_refl_o1 : derivation; 
    r_oeq_refl_o2 : derivation; 
  }
      (**{v
	 o1 :: G |- o1 : T
	            o1 ~ o2
	 o2 :: G |- o2 : T
 	 --------------------------------- oeq_refl (rule 10)
 	       G |- o1 = o2 : T
	 v}*)
and r_oeq_symm = {
    r_oeq_symm_d : derivation;
  }
      (**{v
	 d  :: G |- o1 = o2 : T
 	 --------------------------------- oeq_symm (rule 11)
 	       G |- o2 = o1 : T
	 v}*)
and r_oeq_trans = {
    r_oeq_trans_12 : derivation;
    r_oeq_trans_oeq : derivation;
    r_oeq_trans_23 : derivation;
  }
      (**{v
	 12 :: G |- o1 = o2 : T
	 oeq:: G |- o2 = o2': T
	 23 :: G |- o2'= o3 : T
 	 --------------------------------- oeq_trans (rule 12)
 	       G |- o1 = o3 : T
	 v}*)
and r_o_cast = { 
    r_o_cast_o : derivation; 
    r_o_cast_teq : derivation;
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
  }
      (**{v
	 d :: G |>
	 M :: Ulevel
 	 --------------------------------- u_append (rule 15)
 	      G |- [U](M) type
	 v}*)
and r_u_type = {
    r_u_type_M : uExpr;
    r_u_type_d : derivation; 
  }
      (**{v
	 M :: Ulevel
	 d :: G |>
 	 --------------------------------- u_type (rule 16)
 	      G |- [u](M) : [U](M+1)
	 v}*)
and r_el_u = {
    r_el_u_o : derivation; 
  }
      (**{v
	 o  :: G |- o : [u](M)
 	 --------------------------------- el_u (rule 17)
 	       G |- *o type
	 v}*)
and r_el_u_red = {
    r_el_u_red_M : uExpr; 
    r_el_u_red_o : derivation; 
  }
      (**{v
	 o  :: G |>
 	 --------------------------------- el_u_red M (rule 18)
 	       G |- *[u](M) = [U](M)
	 v}*)
and r_el_u_eq = {
    r_el_u_eq_oeq : derivation; 
  }
      (**{v
	 o  :: G |- o = o' : [u](M)
 	 --------------------------------- el_u_eq (rule 19)
 	       G |- *o = *o'
	 v}*)
and r_el_u_rev_eq = {
    r_el_u_red_eq_M : uExpr; 
    r_el_u_red_eq_o : derivation; 
    r_el_u_red_eq_o' : derivation; 
    r_el_u_red_eq_teq : derivation;
  }
      (**{v
	 M :: uLevel
	 o :: G |- o : [U](M)
	 o':: G |- o': [U](M)
	 oeq  :: G |- *o = *o'
 	 --------------------------------- el_u_rev_eq M (rule 20)
 	       G |- o = o' : [U](M)
	 v}*)
and r_pi_type = {
    r_pi_type_tt : derivation; 
  }
      (**{v
	 tt :: G, x:X |- Y type
 	 --------------------------------- pi_type (rule 21)
 	       G      |- Pi x:X, Y type
	 v}*)
and r_pi_eq = {
    r_pi_eq_teq1 : derivation; 
    r_pi_eq_teq2 : derivation; 
  }
      (**{v
	 teq1 :: G      |- X = X'
	 teq2 :: G, x:X |- Y = Y'
 	 -------------------------------------- pi_eq (rule 22)
 	         G      |- Pi x:X, Y = Pi x:X', Y'
	 v}*)
and r_lambda_type = {
    r_lambda_type_tt : derivation; 
  }
      (**{v
	 tt :: G, x:X, |> o:T
 	 ------------------------------------- lambda_type (rule 23)
 	       G |- lamba x:X, o : Pi x:X, T
	 v}*)






(*inserting here*)



and r_ev = { 
    r_ev_f  : derivation; 
    r_ev_teq : derivation; 		(* it was a suggestion of Andrej Bauer to add this prerequisite *)
    r_ev_o  : derivation;
  }
      (**{v
	 f  :: G |- f : Pi x:T, U
	 teq:: G |- T = T'
	 o  :: G |- o : T'
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

type 'expr derived = 'expr * derivation

(* TEMPLATE
and r_ = {
    r__ : derivation; 
  }
      (**{v
	  :: G |- 
 	 ---------------------------------  (rule )
 	       G |- 
	 v}*)
*)
