# -*- coding: utf-8 -*-

Include "rules/abbreviations.ts".

# A semi-intrinsic encoding of rules, definitions, and theorems.  It's just like the intrinsic
# encoding displayed in judged-expressions.ts, except that we translate the judgements like this:

#    intrinsic			semi-intrinsic

#    a_type			(T:texp) × istype T
#    obj_of_type T		(o:oexp) × hastype o T₁
#    type_equality T U		tequal T₁ U₁
#    object_equality T x y	oequal x₁ y₁ T₁

# Then we will write a tactic for extracting the expression part of a term or type.

Axiom LF ∏_type 

      # ∏_istype { ⊢ T Type } { t : T ⊢ U Type } ⊢ ∏ t:T, U[t] Type .

      : (T:((T':texp) × istype T')) ⟶ (U : ((o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T') ) ⟶ ((T':Singleton(([∏] ($exp T) ($exp U)):texp)) × istype T').

# We make $exp T return T₁.  But what about $exp U?

# What if we make the term_normalization routine do the work?  It would be told
# the type

#     	U : (o : (o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T')

# and then it would receive

#         ($exp U)

# and return the following expression of type oexp ⟶ texp

#     	o ⟼ (U (o UNCAR))
#		      later:  (o UNCAR CAR) ---> o
#		      	      (o UNCAR CDR) ---> internal error

Axiom LF U_type

      # U_istype { ⊢ M Ulevel } ⊢ UU[M] Type.

      : uexp ⟶ ((T':texp) × istype T').

Axiom LF u_object

      #  { ⊢ M Ulevel } ⊢ uu[M] : UU[next[M]].

      : (M:uexp) ⟶ ((o':oexp) × hastype o' (U_type (next M))₁).

Axiom LF El_type

      # { ⊢ M Ulevel, o : UU[M] } ⊢ *o Type.

      : (M:uexp) ⟶ ((o':oexp) × hastype o' (U_type M)₁) ⟶ ((T':texp) × istype T').

Axiom LF El_u_reduction

      #  { ⊢ M Ulevel } [ *uu[M] ≡ UU[M] ].

      : (M:uexp) ⟶ tequal (El_type M (u_object M))₁ (U_type M)₁.

Axiom LF cast

      #  { ⊢ T U Type } [ T ≡ U ] ⇒ { ⊢ o : T } ⊢ o : U.

      : (T:((T':texp) × istype T')) ⟶ (U:((T':texp) × istype T')) ⟶ tequal T₁ U₁ ⟶ ((o':oexp) × hastype o' T₁) ⟶ ((o':oexp) × hastype o' U₁).

Axiom LF forall_object

      #  { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] }
      #    ⊢ @[forall;t][M1,M2,o1,o2[t]] : UU[umax[M1,M2]].

       : (M1:uexp) ⟶ 
         (M2:uexp) ⟶ 
         (o1 : ((o':oexp) × hastype o' (U_type M1)₁)) ⟶ 
	 (o2 : ((o':oexp) × hastype o' (El_type M1 o1)₁) ⟶ ((o':oexp) × hastype o' (U_type M2)₁)) 
  	 ⟶ ((o':oexp) × hastype o' (U_type (umax M1 M2))₁).

Axiom LF λ_object

      # { ⊢ T Type } { x : T ⊢ U Type, o : U[x] } ⊢ λ t:T, o[t] : ∏ t:T, U[t].

      : (T:((T':texp) × istype T')) ⟶ 
      	(U : ((o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(body : (t:((o':oexp) × hastype o' T₁)) ⟶ ((o':oexp) × hastype o' (U t)₁)) 
	⟶ ((o':oexp) × hastype o' (∏_type T U)₁).

Axiom LF ev_object

      #  { ⊢ T Type } { t : T ⊢ U Type } { ⊢ f : ∏ t:T, U[t], o : T } ⊢ @[ev;t][f,o,U[t]] : U[o].

      : (T:((T':texp) × istype T')) ⟶ 
      	(U : ((o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(f : ((o':oexp) × hastype o' (∏_type T U)₁)) ⟶ 
	(arg : ((o':oexp) × hastype o' T₁)) 
	⟶ ((o':oexp) × hastype o' (U arg)₁).

Axiom LF beta_reduction

      # { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U[x] }
      #   [ @[ev;t][(λ t:T, o2[t]), o1, U[t]] ≡ o2[o1] : U[o1] ].

       : (T:((T':texp) × istype T')) ⟶ 
       	 (arg : ((o':oexp) × hastype o' T₁)) ⟶ 
	 (U : ((o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T')) ⟶ 
	 (body : (t:((o':oexp) × hastype o' T₁)) ⟶ ((o':oexp) × hastype o' (U t)₁)) 
	 ⟶ oequal (U arg)₁ (ev_object T U (λ_object T U body) arg)₁ (body arg)₁.

# introduce non-dependent versions of ∏_type, λ_object, and ev_object:

Definition LF arrow_type

	   : (T:((T':texp) × istype T')) ⟶ (U:((T':texp) × istype T')) ⟶ ((T':texp) × istype T') 

	   := T ⟼ U ⟼ (∏_type T (_ ⟼ U)).

Definition LF simple_λ_object

	   : (T:((T':texp) × istype T')) ⟶ 
	     (U:((T':texp) × istype T')) ⟶ 
	     (body : (t:((o':oexp) × hastype o' T₁)) ⟶ ((o':oexp) × hastype o' U₁)) ⟶ 
	     ((o':oexp) × hastype o' (arrow_type T U)₁) 

	   := T ⟼ U ⟼ (λ_object T (_ ⟼ U)).

Definition LF simple_ev_object

	   : (T:((T':texp) × istype T')) ⟶ 
	     (U:((T':texp) × istype T')) ⟶ 
	     (f : ((o':oexp) × hastype o' (arrow_type T U)₁)) ⟶ 
	     (arg : ((o':oexp) × hastype o' T₁)) ⟶ 
	     ((o':oexp) × hastype o' U₁)

	   := T ⟼ U ⟼ (ev_object T (_ ⟼ U)).

Theorem LF modus_ponens

	: (T:((T':texp) × istype T')) ⟶ 
	  (U:((T':texp) × istype T')) ⟶ 
	  (V:((T':texp) × istype T')) ⟶ 
	  ((o':oexp) × hastype o' 
	    (arrow_type 
	    	(arrow_type T U) 
		(arrow_type 
		   (arrow_type U V) 
		   (arrow_type T V)))₁) 

	:= T ⟼ U ⟼ V ⟼ 
	   (simple_λ_object (arrow_type T U)
	       (arrow_type (arrow_type U V) (arrow_type T V))
	       (f ⟼ (simple_λ_object (arrow_type U V)
		       (arrow_type T V)
		       (g ⟼ (simple_λ_object T V 
			       (t ⟼ (simple_ev_object U V g (simple_ev_object T U f t)))))))).

Axiom LF El_forall_reduction

       # { ⊢ M1 M2 Ulevel, o1 : UU[M1] } { x : *o1 ⊢ o2 : UU[M2] }

       : (M1:uexp) ⟶ 
         (M2:uexp) ⟶ 
	 (o1 : ((o':oexp) × hastype o' (U_type M1)₁)) ⟶ 
	 (o2 : ((o':oexp) × hastype o' (El_type M1 o1)₁) ⟶ ((o':oexp) × hastype o' (U_type M2)₁)) 
	⟶ tequal 
		 (El_type (umax M1 M2) (forall_object M1 M2 o1 o2))₁
		 (∏_type (El_type M1 o1) (x ⟼ (El_type (umax M1 M2) (o2 x))))₁.

Lemma LF A : (u:uexp) ⟶ (T : ((o':oexp) × hastype o' (U_type u)₁)) ⟶ (U : ((o':oexp) × hastype o' (U_type u)₁))
		      ⟶ (f : ((o':oexp) × hastype o' (El_type u (forall_object u u T (_ ⟼ U)))₁))
		      ⟶ ((o':oexp) × hastype o' (∏_type (El_type u T) (_ ⟼ (El_type u U)))₁)

          := u ⟼ T ⟼ U ⟼ 
		 (cast (El_type u (forall_object u u T (_ ⟼ U))) 
                       (∏_type (El_type u T) (_ ⟼ (El_type u U)))
                       (El_forall_reduction u u T (_ ⟼ U))).

Theorem LF compose3 : (u:uexp) ⟶ 
		      (T : ((o':oexp) × hastype o' (U_type u)₁)) ⟶ 
		      (U : ((o':oexp) × hastype o' (U_type u)₁)) ⟶ 
		      (V : ((o':oexp) × hastype o' (U_type u)₁)) ⟶ 
		      (g : ((o':oexp) × hastype o' (El_type u (forall_object u u U (_ ⟼ V)))₁)) ⟶
		      (f : ((o':oexp) × hastype o' (El_type u (forall_object u u T (_ ⟼ U)))₁)) ⟶
		      (t : ((o':oexp) × hastype o' (El_type u T)₁)) ⟶
		      ((o':oexp) × hastype o' (El_type u V)₁)
      := u ⟼ T ⟼ U ⟼ V ⟼ g ⟼ f ⟼ t ⟼ 
	     (ev_object 
	     	(El_type u U) 
		(_ ⟼ (El_type u V)) 
		(A u U V g) 
		(ev_object (El_type u T) (_ ⟼ (El_type u U)) (A u T U f) t)) .

Axiom LF 6.3.1 Σ_type

      # { ⊢ T Type } { t : T ⊢ U Type } ⊢ Σ t:T, U[t] Type .

      : (T : ((T':texp) × istype T')) ⟶ ( ((o':oexp) × hastype o' T₁) ⟶ ((T':texp) × istype T') ) ⟶ ((T':texp) × istype T').

Axiom LF 6.3.2 pair_object

      # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } ⊢ @[pair][o1,o2,T2] : Σ x:T1, T2[x].

      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(o1 : ((o':oexp) × hastype o' T1₁)) ⟶
        (o2 : ((o':oexp) × hastype o' (T2 o1)₁))
	⟶ ((o':oexp) × hastype o' (Σ_type T1 T2)₁).

Axiom LF 6.3.3 pr1_object

      # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] } ⊢ @[pr1][T1,T2,a] : T1.

      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(a : ((o':oexp) × hastype o' (Σ_type T1 T2)₁))
	 ⟶ ((o':oexp) × hastype o' T1₁).

Axiom LF 6.3.4 pr2_object

      # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] } 
      # ⊢ @[pr2][T1,T2,a] : T2[@[pr1][T1,T2,a]].

      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(a : ((o':oexp) × hastype o' (Σ_type T1 T2)₁))
	 ⟶ ((o':oexp) × hastype o' (T2 (pr1_object T1 T2 a))₁).

Axiom LF 6.3.5 pr1_pair_reduction

       # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } 
       # [ @[pr1][T1,T2,@[pair][o1,o2,T2]] ≡ o1 : T1 ].

      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
        (o1 : ((o':oexp) × hastype o' T1₁)) ⟶
        (o2 : ((o':oexp) × hastype o' (T2 o1)₁)) ⟶
        oequal T1₁
	   (pr1_object T1 T2 (pair_object T1 T2 o1 o2))₁
	   o1₁.

Axiom LF parametrized_tequal			    # new axiom
      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
	(o : ((o':oexp) × hastype o' T1₁)) ⟶
	(o' : ((o':oexp) × hastype o' T1₁)) ⟶
	(oequal T1₁ o₁ o'₁) ⟶
	(tequal (T2 o)₁ (T2 o')₁).        

Axiom LF 6.3.6 pr2_pair_reduction

      # { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] } 
      # [ @[pr2][T1,T2,@[pair][o1,o2,T2]] ≡ o2 : T2[o1] ].

      : (T1 : ((T':texp) × istype T')) ⟶ 
        (T2 : ((o':oexp) × hastype o' T1₁) ⟶ ((T':texp) × istype T')) ⟶ 
        (o1 : ((o':oexp) × hastype o' T1₁)) ⟶
        (o2 : ((o':oexp) × hastype o' (T2 o1)₁)) ⟶
        oequal (T2 o1)₁
	   (cast
	       (T2 (pr1_object T1 T2 (pair_object T1 T2 o1 o2)))
	       (T2 o1)
	       (parametrized_tequal
	       	  T1 T2 (pr1_object T1 T2 (pair_object T1 T2 o1 o2)) o1
		  (pr1_pair_reduction T1 T2 o1 o2))
	       (pr2_object T1 T2 (pair_object T1 T2 o1 o2)))₁
	   o2₁.

Axiom LF 11.5.1 paths_object

      # { ⊢ M Ulevel, t : UU[M], o1 o2 : *t } ⊢ @[paths][M,t,o1,o2] : UU[M].

      : (M:uexp) ⟶ 
        (t : ((o':oexp) × hastype o' (U_type M)₁)) ⟶
      	(o1 : ((o':oexp) × hastype o' (El_type M t)₁)) ⟶
      	(o2 : ((o':oexp) × hastype o' (El_type M t)₁)) ⟶
	((o':oexp) × hastype o' (U_type M)₁).

Axiom LF 11.5.2 Id_type

      # { ⊢ T Type, o1 o2 : T } ⊢ @[Id][T,o1,o2] Type.

      : (T : ((T':texp) × istype T')) ⟶ 
        (o1 : ((o':oexp) × hastype o' T₁)) ⟶ 
	(o2 : ((o':oexp) × hastype o' T₁)) ⟶
        ((T':texp) × istype T').

Axiom LF 11.5.3 refl_object

      # { ⊢ T Type, o : T } ⊢ @[refl][T,o] : @[Id][T,o,o].

      : (T : ((T':texp) × istype T')) ⟶ 
        (o : ((o':oexp) × hastype o' T₁)) ⟶ 
	((o':oexp) × hastype o' (Id_type T o o)₁).

Axiom LF 11.5.4 J_object

      # { ⊢ T Type, a b:T, i:@[Id][T,a,b] } { x:T, e:@[Id][T,a,x] ⊢ S Type } 
      # { ⊢ q : S[a,@[refl][T,a]] }
      #   ⊢ @[J][T,a,b,q,i,S] : S[b,i].

      : (T : ((T':texp) × istype T')) ⟶ 
        (a : ((o':oexp) × hastype o' T₁)) ⟶ 
	(b : ((o':oexp) × hastype o' T₁)) ⟶ 
        (i : ((o':oexp) × hastype o' (Id_type T a b)₁)) ⟶
	(x : ((o':oexp) × hastype o' T₁)) ⟶
	(S : (x : ((o':oexp) × hastype o' T₁)) ⟶ ((o':oexp) × hastype o' (Id_type T a x)₁) ⟶ ((T':texp) × istype T')) ⟶
	(q : ((o':oexp) × hastype o' (S a (refl_object T a))₁)) ⟶
	((o':oexp) × hastype o' (S b i)₁).

Definition LF Iscontr

      # { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type

      : (X : ((T':texp) × istype T')) ⟶ ((T':texp) × istype T')

      := X ⟼ (Σ_type X (x ⟼ (∏_type X (y ⟼ (Id_type X y x))))).

Definition LF Hfiber

      # { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_][f,x,Y]=y  Type 

      : (X : ((T':texp) × istype T')) ⟶ (Y : ((T':texp) × istype T')) ⟶
        (f : ((o':oexp) × hastype o' (arrow_type X Y)₁)) ⟶
	(y : ((o':oexp) × hastype o' Y₁)) ⟶
	  ((T':texp) × istype T')

      := X ⟼ Y ⟼ f ⟼ y ⟼ (Σ_type X (x ⟼ (Id_type Y (simple_ev_object X Y f x) y))).

Definition LF Isweq

	# { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr₁[Hfiber₁[X,Y,f,y]] Type 

      : (X : ((T':texp) × istype T')) ⟶ (Y : ((T':texp) × istype T')) ⟶
        (f : ((o':oexp) × hastype o' (arrow_type X Y)₁)) ⟶
	((T':texp) × istype T')

      := X ⟼ Y ⟼ f ⟼ (∏_type Y (y ⟼ (Iscontr (Hfiber X Y f y)))).

Definition LF Weq

      # { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq₁[X,Y,f] Type 

      : (X : ((T':texp) × istype T')) ⟶ (Y : ((T':texp) × istype T')) ⟶ ((T':texp) × istype T')

      := X ⟼ Y ⟼ (Σ_type (arrow_type X Y) (f ⟼ (Isweq X Y f))).

Definition LF idfun

      # { ⊢ X Type } ⊢ λ x:X,x : X⟶X

      : (X : ((T':texp) × istype T')) ⟶ ((o':oexp) × hastype o' (arrow_type X X)₁)

      := X ⟼ (simple_λ_object X X (x ⟼ x)).

Theorem LF idisweq

      # { ⊢ X Type } : Isweq₁[X,X,idfun₁[X]] 

      : (X : ((T':texp) × istype T')) ⟶ ((o':oexp) × hastype o' (Isweq X X (idfun X))₁)

      := $admit.

      # := X |-> ($apply λ_object).
      # := X |-> $fail.
      # := ($fail λ_object _ _ _).
      # := X |-> (λ_object _ _ _). 
      # := X |-> (λ_object X (y ⟼ (Iscontr (Hfiber X X (idfun X) y))) (y ⟼ _)). 
      # := $( intro ; fail ) .

End.

#   Local Variables:
#   compile-command: "make -C .. semi-intrinsic "
#   End:
