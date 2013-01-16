# -*- coding: utf-8 -*-

Include "rules/abbreviations.ts".

# new "judged expression" level:

Axiom LF ∏_type # ∏_istype { ⊢ T Type } { t : T ⊢ U Type } ⊢ ∏ t:T, U[t] Type .
      : (T:a_type) ⟶ ( obj_of_type T ⟶ a_type ) ⟶ a_type.

Axiom LF U_type # U_istype { ⊢ M Ulevel } ⊢ UU[M] Type.
      : uexp ⟶ a_type.

Axiom LF u_object		       #  { ⊢ M Ulevel } ⊢ uu[M] : UU[next[M]].
       : (M:uexp) ⟶ obj_of_type (U_type (next M)).

Axiom LF El_type			 # { ⊢ M Ulevel, o : UU[M] } ⊢ *o Type.
      : (M:uexp) ⟶ obj_of_type (U_type M) ⟶ a_type.

Axiom LF El_u_reduction			  #  { ⊢ M Ulevel } [ *uu[M] ≡ UU[M] ].
       : (M:uexp) ⟶ type_equality (El_type M (u_object M)) (U_type M).

Axiom LF cast		     #  { ⊢ T U Type } [ T ≡ U ] ⇒ { ⊢ o : T } ⊢ o : U.
       : (T:a_type) ⟶ (U:a_type) ⟶ type_equality T U ⟶ obj_of_type T ⟶ obj_of_type U.

Axiom LF forall_object #  { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] } ⊢ @[forall;t][M1,M2,o1,o2[t]] : UU[umax[M1,M2]].
       : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (U_type M1)) ⟶ (o2 : obj_of_type (El_type M1 o1) ⟶ obj_of_type (U_type M2)) 
      		   ⟶ obj_of_type (U_type (umax M1 M2)).

Axiom LF λ_object # { ⊢ T Type } { x : T ⊢ U Type, o : U[x] } ⊢ λ t:T, o[t] : ∏ t:T, U[t].
       : (T:a_type) ⟶ 
      		(U : obj_of_type T ⟶ a_type) ⟶ 
		(body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	   ⟶ obj_of_type (∏_type T U).

Axiom LF ev_object #  { ⊢ T Type } { t : T ⊢ U Type } { ⊢ f : ∏ t:T, U[t], o : T } ⊢ @[ev;t][f,o,U[t]] : U[o].
      : (T:a_type) ⟶ 
      	      (U : obj_of_type T ⟶ a_type) ⟶ 
	      (f : obj_of_type (∏_type T U)) ⟶ 
	      (arg : obj_of_type T) 
	   ⟶ obj_of_type (U arg).

Axiom LF beta_reduction	# { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U[x] } [ @[ev;t][(λ t:T, o2[t]), o1, U[t]] ≡ o2[o1] : U[o1] ].
       : (T:a_type) ⟶ 
       	    (arg : obj_of_type T) ⟶ 
	    (U : obj_of_type T ⟶ a_type) ⟶ 
	    (body : (t:obj_of_type T) ⟶ obj_of_type (U t)) 
	     ⟶ object_equality (U arg) (ev_object T U (λ_object T U body) arg) (body arg).

# introduce non-dependent versions of ∏_type, λ_object, and ev_object:

Definition LF arrow_type : (T:a_type) ⟶ (U:a_type) ⟶ a_type := T ⟼ U ⟼ (∏_type T (_ ⟼ U)).

Definition LF simple_λ_object : (T:a_type) ⟶ (U:a_type) ⟶ (body : (t:obj_of_type T) ⟶ obj_of_type U) ⟶ obj_of_type (arrow_type T U) :=
	   T ⟼ U ⟼ (λ_object T (_ ⟼ U)).

Definition LF simple_ev_object : (T:a_type) ⟶ (U:a_type) ⟶ (f : obj_of_type (arrow_type T U)) ⟶ (arg : obj_of_type T) ⟶ obj_of_type U :=
	   T ⟼ U ⟼ (ev_object T (_ ⟼ U)).

Theorem LF modus_ponens : (T:a_type) ⟶ (U:a_type) ⟶ (V:a_type) ⟶ obj_of_type (arrow_type (arrow_type T U) (arrow_type (arrow_type U V) (arrow_type T V))) :=
	T ⟼ U ⟼ V ⟼ 
	(simple_λ_object (arrow_type T U)
	       (arrow_type (arrow_type U V) (arrow_type T V))
	       (f ⟼ (simple_λ_object (arrow_type U V)
	       		   (arrow_type T V)
			   (g ⟼ (simple_λ_object T V 
			   	       (t ⟼ (simple_ev_object U V g (simple_ev_object T U f t)))))))).

Axiom LF El_forall_reduction # { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] }
       : (M1:uexp) ⟶ (M2:uexp) ⟶ (o1 : obj_of_type (U_type M1))
      	⟶ (o2 : obj_of_type (El_type M1 o1) ⟶ obj_of_type (U_type M2)) 
	⟶ type_equality (El_type (umax M1 M2) (forall_object M1 M2 o1 o2)) (∏_type (El_type M1 o1) (x ⟼ (El_type (umax M1 M2) (o2 x)))).

Lemma LF A : (u:uexp) ⟶ (T : obj_of_type (U_type u)) ⟶ (U : obj_of_type (U_type u))
		      ⟶ (f : obj_of_type (El_type u (forall_object u u T (_ ⟼ U))))
		      ⟶ obj_of_type (∏_type (El_type u T) (_ ⟼ (El_type u U))) :=
                 u ⟼ T ⟼ U ⟼ 
		 (cast (El_type u (forall_object u u T (_ ⟼ U))) 
                       (∏_type (El_type u T) (_ ⟼ (El_type u U)))
                       (El_forall_reduction u u T (_ ⟼ U))).

Theorem LF compose3 : (u:uexp) ⟶ (T : obj_of_type (U_type u)) ⟶ (U : obj_of_type (U_type u)) ⟶ (V : obj_of_type (U_type u)) ⟶ 
		      (g : obj_of_type (El_type u (forall_object u u U (_ ⟼ V)))) ⟶
		      (f : obj_of_type (El_type u (forall_object u u T (_ ⟼ U)))) ⟶
		      (t : obj_of_type (El_type u T)) ⟶
		      obj_of_type (El_type u V) := 
                 u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
		      (ev_object (El_type u U) (_ ⟼ (El_type u V)) (A u U V g) (ev_object (El_type u T) (_ ⟼ (El_type u U)) (A u T U f) t)) .

Axiom LF 6.3.1 Σ_type # { ⊢ T Type } { t : T ⊢ U Type } ⊢ Σ t:T, U[t] Type .
      : (T : a_type) ⟶ ( obj_of_type T ⟶ a_type ) ⟶ a_type.

Axiom LF 6.3.2 pair_object # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } ⊢ @[pair][o1,o2,T2] : Σ x:T1, T2[x].
      : (T1 : a_type) ⟶ (T2 : obj_of_type T1 ⟶ a_type) ⟶ (o1 : obj_of_type T1) ⟶
        (o2 : obj_of_type (T2 o1)) ⟶ obj_of_type (Σ_type T1 T2).

Axiom LF 6.3.3 pr1_object # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] } ⊢ @[pr1][T1,T2,a] : T1.
      : (T1 : a_type) ⟶ (T2 : obj_of_type T1 ⟶ a_type) ⟶ (a : obj_of_type (Σ_type T1 T2)) ⟶
        obj_of_type T1.

Axiom LF 6.3.4 pr2_object # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] } 
      			   # ⊢ @[pr2][T1,T2,a] : T2[@[pr1][T1,T2,a]].
      : (T1 : a_type) ⟶ (T2 : obj_of_type T1 ⟶ a_type) ⟶ (a : obj_of_type (Σ_type T1 T2)) ⟶
        obj_of_type (T2 (pr1_object T1 T2 a)).

Axiom LF 6.3.5 pr1_pair_reduction # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } 
      				  # [ @[pr1][T1,T2,@[pair][o1,o2,T2]] ≡ o1 : T1 ].
      : (T1 : a_type) ⟶ 
        (T2 : obj_of_type T1 ⟶ a_type) ⟶ 
        (o1 : obj_of_type T1) ⟶
        (o2 : obj_of_type (T2 o1)) ⟶
        object_equality
	   T1
	   (pr1_object T1 T2 (pair_object T1 T2 o1 o2))
	   o1.

Axiom LF parametrized_type_equality			    # a new kind of axiom!
      : (T1 : a_type) ⟶ 
        (T2 : obj_of_type T1 ⟶ a_type) ⟶ 
	(o : obj_of_type T1) ⟶
	(o' : obj_of_type T1) ⟶
	(object_equality T1 o o') ⟶
	(type_equality (T2 o) (T2 o')).        

Axiom LF 6.3.6 pr2_pair_reduction # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } 
      				  # [ @[pr2][T1,T2,@[pair][o1,o2,T2]] ≡ o2 : T2[o1] ].
      : (T1 : a_type) ⟶ 
        (T2 : obj_of_type T1 ⟶ a_type) ⟶ 
        (o1 : obj_of_type T1) ⟶
        (o2 : obj_of_type (T2 o1)) ⟶
        object_equality
	   (T2 o1)
	   (cast
	       (T2 (pr1_object T1 T2 (pair_object T1 T2 o1 o2)))
	       (T2 o1)
	       (parametrized_type_equality
	       	  T1 T2 (pr1_object T1 T2 (pair_object T1 T2 o1 o2)) o1
		  (pr1_pair_reduction T1 T2 o1 o2))
	       (pr2_object T1 T2 (pair_object T1 T2 o1 o2)))
	   o2.

Axiom LF 11.5.1 paths_object  # { ⊢ M Ulevel, t : UU[M], o1 o2 : *t } ⊢ @[paths][M,t,o1,o2] : UU[M].
      : (M:uexp) ⟶ (t : obj_of_type (U_type M)) ⟶
      	(o1 : obj_of_type (El_type M t)) ⟶
      	(o2 : obj_of_type (El_type M t)) ⟶
	obj_of_type (U_type M).

Axiom LF 11.5.2 Id_type # { ⊢ T Type, o1 o2 : T } ⊢ @[Id][T,o1,o2] Type.
      : (T : a_type) ⟶ (o1 : obj_of_type T) ⟶ (o2 : obj_of_type T) ⟶
        a_type.

Axiom LF 11.5.3 refl_object # { ⊢ T Type, o : T } ⊢ @[refl][T,o] : @[Id][T,o,o].
      : (T : a_type) ⟶ (o : obj_of_type T) ⟶ obj_of_type (Id_type T o o).

Axiom LF 11.5.4 J_object # { ⊢ T Type, a b:T, i:@[Id][T,a,b] } { x:T, e:@[Id][T,a,x] ⊢ S Type } 
      			  # { ⊢ q : S[a,@[refl][T,a]] }
      			  #   ⊢ @[J][T,a,b,q,i,S] : S[b,i].
      : (T : a_type) ⟶ (a : obj_of_type T) ⟶ (b : obj_of_type T) ⟶ 
        (i : obj_of_type (Id_type T a b)) ⟶
	(x : obj_of_type T) ⟶
	(S : (x : obj_of_type T) ⟶ obj_of_type (Id_type T a x) ⟶ a_type) ⟶
	(q : obj_of_type (S a (refl_object T a))) ⟶
	obj_of_type (S b i).

Definition LF Iscontr # { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type
      : (X : a_type) ⟶ a_type
      := X ⟼ (Σ_type X (x ⟼ (∏_type X (y ⟼ (Id_type X y x))))).

Definition LF Hfiber # { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_][f,x,Y]=y  Type 
      : (X : a_type) ⟶ (Y : a_type) ⟶
        (f : obj_of_type (arrow_type X Y)) ⟶
	(y : obj_of_type Y) ⟶
	  a_type
      := X ⟼ Y ⟼ f ⟼ y ⟼ (Σ_type X (x ⟼ (Id_type Y (simple_ev_object X Y f x) y))).

Definition LF Isweq # { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr₁[Hfiber₁[X,Y,f,y]] Type 
      : (X : a_type) ⟶ (Y : a_type) ⟶
        (f : obj_of_type (arrow_type X Y)) ⟶
	a_type
      := X ⟼ Y ⟼ f ⟼ (∏_type Y (y ⟼ (Iscontr (Hfiber X Y f y)))).

Definition LF Weq # { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq₁[X,Y,f] Type 
      : (X : a_type) ⟶ (Y : a_type) ⟶ a_type
      := X ⟼ Y ⟼ (Σ_type (arrow_type X Y) (f ⟼ (Isweq X Y f))).

Definition LF idfun # { ⊢ X Type } ⊢ λ x:X,x : X⟶X
      : (X : a_type) ⟶ obj_of_type (arrow_type X X)
      := X ⟼ (simple_λ_object X X (x ⟼ x)).

Theorem LF idisweq # { ⊢ X Type } : Isweq₁[X,X,idfun₁[X]] 
      : (X : a_type) ⟶ obj_of_type (Isweq X X (idfun X))
#      := X |-> ($apply λ_object).
      := $admit.
End.      
      := X |-> $fail.
      := ($fail λ_object _ _ _).
      := X |-> (λ_object _ _ _). 
      := X |-> (λ_object X (y ⟼ (Iscontr (Hfiber X X (idfun X) y))) (y ⟼ _)). 
      := $( intro ; fail ) .

End.

#   Local Variables:
#   compile-command: "make -C .. judged-expressions "
#   End:
