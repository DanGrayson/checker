# -*- coding: utf-8 -*-

Include "rules/abbreviations.ts".

# new "judged expression" level:

Axiom LF pi_type # ∏_istype { ⊢ T Type } { t : T ⊢ U Type } ⊢ ∏ t:T, U[t] Type .
      : (T:a_type) ⟶ ( obj_of_type T ⟶ a_type ) ⟶ a_type.

Axiom LF U_type # U_istype { ⊢ M Ulevel } ⊢ UU[M] Type.
      : uexp ⟶ a_type.

Axiom LF u_hastype		       #  { ⊢ M Ulevel } ⊢ uu[M] : UU[next[M]].
       : (M:uexp) ⟶ obj_of_type (U_type (next M)).

Axiom LF El_istype			 # { ⊢ M Ulevel, o : UU[M] } ⊢ *o Type.
      : (M:uexp) ⟶ obj_of_type (U_type M) ⟶ a_type.

Axiom LF El_u_reduction			  #  { ⊢ M Ulevel } [ *uu[M] ≡ UU[M] ].
       : (M:uexp) ⟶ type_equality (El_istype M (u_hastype M)) (U_type M).

Axiom LF cast		     #  { ⊢ T U Type } [ T ≡ U ] ⇒ { ⊢ o : T } ⊢ o : U.
       : (T:a_type) ⟶ (U:a_type) ⟶ type_equality T U ⟶ obj_of_type T ⟶ obj_of_type U.

Axiom LF forall_hastype #  { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] } ⊢ @[forall;t][M1,M2,o1,o2[t]] : UU[umax[M1,M2]].
       : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (U_type M1)) ⟶ (o2 : obj_of_type (El_istype M1 o1) ⟶ obj_of_type (U_type M2)) 
      		   ⟶ obj_of_type (U_type (umax M1 M2)).

Axiom LF λ_hastype # { ⊢ T Type } { x : T ⊢ U Type, o : U[x] } ⊢ λ t:T, o[t] : ∏ t:T, U[t].
       : (T:a_type) ⟶ 
      		(U : obj_of_type T ⟶ a_type) ⟶ 
		(body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	   ⟶ obj_of_type (pi_type T U).

Axiom LF ev_hastype #  { ⊢ T Type } { t : T ⊢ U Type } { ⊢ f : ∏ t:T, U[t], o : T } ⊢ @[ev;t][f,o,U[t]] : U[o].
      : (T:a_type) ⟶ 
      	      (U : obj_of_type T ⟶ a_type) ⟶ 
	      (f : obj_of_type (pi_type T U)) ⟶ 
	      (arg : obj_of_type T) 
	   ⟶ obj_of_type (U arg).

Axiom LF beta_reduction	# { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U[x] } [ @[ev;t][(λ t:T, o2[t]), o1, U[t]] ≡ o2[o1] : U[o1] ].
       : (T:a_type) ⟶ 
       	    (arg : obj_of_type T) ⟶ 
	    (U : obj_of_type T ⟶ a_type) ⟶ 
	    (body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	     ⟶ object_equality (U arg) (ev_hastype T U (λ_hastype T U body) arg) (body arg).

Theorem LF id0 : (T:a_type) ⟶ (t:obj_of_type T) ⟶ obj_of_type T := _ ⟼ t ⟼ t.

Theorem LF id0' : (u:uexp) ⟶ (T:obj_of_type (U_type u)) ⟶ (t:obj_of_type (El_istype u T)) ⟶ obj_of_type (El_istype u T) := _ ⟼ _ ⟼ t ⟼ t.

Theorem LF id3' : (u:uexp) ⟶ (T:obj_of_type (U_type u)) ⟶ (T':obj_of_type (U_type u)) ⟶ (f:obj_of_type (pi_type (El_istype u T) (_ ⟼ (El_istype u T'))))
			   ⟶ (t:obj_of_type (El_istype u T)) ⟶ obj_of_type (El_istype u T') :=
	u ⟼ T ⟼ T' ⟼ (ev_hastype (El_istype u T) (_ ⟼ (El_istype u T'))).

Theorem LF make : (T:a_type) ⟶ (U:a_type) ⟶ (f : obj_of_type T ⟶ obj_of_type U) ⟶ obj_of_type (pi_type T (_ ⟼ U)) := 
	T ⟼ U ⟼ (λ_hastype T (_ ⟼ U)).

# introduce non-dependent versions of pi_type, λ_hastype, and ev_hastype:

Definition LF pi1 : (T:a_type) ⟶ (U:a_type) ⟶ a_type := T ⟼ U ⟼ (pi_type T (_ ⟼ U)).

Definition LF lamb1 : (T:a_type) ⟶ (U:a_type) ⟶ (body : (t:obj_of_type T) ⟶ obj_of_type U) ⟶ obj_of_type (pi1 T U) :=
	   T ⟼ U ⟼ (λ_hastype T (_ ⟼ U)).

Definition LF ev1 : (T:a_type) ⟶ (U:a_type) ⟶ (f : obj_of_type (pi1 T U)) ⟶ (arg : obj_of_type T) ⟶ obj_of_type U :=
	   T ⟼ U ⟼ (ev_hastype T (_ ⟼ U)).

Theorem LF modus_ponens : (T:a_type) ⟶ (U:a_type) ⟶ (V:a_type) ⟶ obj_of_type (pi1 (pi1 T U) (pi1 (pi1 U V) (pi1 T V))) :=
	T ⟼ U ⟼ V ⟼ 
	(lamb1 (pi1 T U)
	       (pi1 (pi1 U V) (pi1 T V))
	       (f ⟼ (lamb1 (pi1 U V)
	       		   (pi1 T V)
			   (g ⟼ (lamb1 T V 
			   	       (t ⟼ (ev1 U V g (ev1 T U f t)))))))).

Axiom LF El_forall_reduction # { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] }
       : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (U_type M1))
      	⟶ (o2 : obj_of_type (El_istype M1 o1) ⟶ obj_of_type (U_type M2)) 
	⟶ type_equality (El_istype (umax M1 M2) (forall_hastype M1 M2 o1 o2)) (pi_type (El_istype M1 o1) (x ⟼ (El_istype (umax M1 M2) (o2 x)))).

Lemma LF A : (u:uexp) ⟶ (T : obj_of_type (U_type u)) ⟶ (U : obj_of_type (U_type u))
		      ⟶ (f : obj_of_type (El_istype u (forall_hastype u u T (_ ⟼ U))))
		      ⟶ obj_of_type (pi_type (El_istype u T) (_ ⟼ (El_istype u U))) :=
                 u ⟼ T ⟼ U ⟼ 
		 (cast (El_istype u (forall_hastype u u T (_ ⟼ U))) 
                       (pi_type (El_istype u T) (_ ⟼ (El_istype u U)))
                       (El_forall_reduction u u T (_ ⟼ U))).

Theorem LF compose3 : (u:uexp) ⟶ (T : obj_of_type (U_type u)) ⟶ (U : obj_of_type (U_type u)) ⟶ (V : obj_of_type (U_type u)) ⟶ 
		      (g : obj_of_type (El_istype u (forall_hastype u u U (_ ⟼ V)))) ⟶
		      (f : obj_of_type (El_istype u (forall_hastype u u T (_ ⟼ U)))) ⟶
		      (t : obj_of_type (El_istype u T)) ⟶
		      obj_of_type (El_istype u V) := 
                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
		      (ev_hastype (El_istype u U) (_ ⟼ (El_istype u V)) (A u U V g) (ev_hastype (El_istype u T) (_ ⟼ (El_istype u U)) (A u T U f) t)) .

Axiom LF 11.5.1 paths_hastype  # { ⊢ M Ulevel, t : UU[M], o1 o2 : *t } ⊢ @[paths][M,t,o1,o2] : UU[M].
      : (M:uexp) -> (t : obj_of_type (U_type M)) ->
      	(o1 : obj_of_type (El_istype M t)) ->
      	(o2 : obj_of_type (El_istype M t)) ->
	obj_of_type (U_type M).

Axiom LF 11.5.2 Id_istype # { ⊢ T Type, o1 o2 : T } ⊢ @[Id][T,o1,o2] Type.
      : (T : a_type) -> (o1 : obj_of_type T) -> (o2 : obj_of_type T) ->
        a_type.

Axiom LF 11.5.3 refl_hastype # { ⊢ T Type, o : T } ⊢ @[refl][T,o] : @[Id][T,o,o].
      : (T : a_type) -> (o : obj_of_type T) -> obj_of_type (Id_istype T o o).

Axiom LF 11.5.4 J_hastype # { ⊢ T Type, a b:T, i:@[Id][T,a,b] } { x:T, e:@[Id][T,a,x] ⊢ S Type } { ⊢ q : S[a,@[refl][T,a]] } ⊢ @[J][T,a,b,q,i,S] : S[b,i].
      : (T : a_type) -> (a : obj_of_type T) -> (b : obj_of_type T) -> 
        (i : obj_of_type (Id_istype T a b)) ->
	(x : obj_of_type T) ->
	(S : (x : obj_of_type T) -> obj_of_type (Id_istype T a x) -> a_type ) ->
	(q : obj_of_type (S a (refl_hastype T a))) ->
	obj_of_type (S b i).

#   Local Variables:
#   compile-command: "make -C .. judged-expressions "
#   End:
