# -*- coding: utf-8 -*-


# the next 4 examples show how the new TS syntax for derivations is 24% smaller than the corresponding LF syntax
# it's designed to replace

Define compose1 (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := [ev;_](g,[ev;_](f,t,U),V) : V ;; (
       # LF syntax
       ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) $a (ev_hastype T (_ ⟼ U) f t $a $a)).

Define compose1' (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := [ev;_](g,[ev;_](f,t,U),V) : V ;
       # new TS syntax
       [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a)).

Define compose2 (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;;
      # LF syntax
      (λ_hastype T (_ ⟼ V) (t ⟼ ([ev] g ([ev] f t (_ ⟼ U)) (_ ⟼ V)) ) $a (t ⟼ _ ⟼ (ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) $a (ev_hastype T (_ ⟼ U) f t $a $a )))).

Define compose2' (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;
      # new TS syntax
      [λ_hastype](T, _ ⟾ V, t ⟾ g (f t), $a, t ⟾ _ ⟾ [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a))).


Define A (u : Ulevel; u=u) (t : [U](u)) := [El](t);; (El_type u $a $0).

Define A'(u : Ulevel; u=u) (t : [U](u)) := [El](t); [El_type](u, $a, $0).

Variable u1 : Ulevel.

Define C := [u](u1) : [U]([next](u1));; (u_univ $a).

Define B (u : Ulevel) (t : [U](u)) := [El](t);; (El_type u $a $0).

Check LF (B ([next] u1) ([u] u1) (u_univ u1)).

Check LF ∏_istype.

Define E (u1 u2 u3:Ulevel)(K:Type) := K⟶K;; (∏_istype $a (_ ⟼ $a) (_ ⟼ _ ⟼ $a) ).

Define E'(u1 u2 u3:Ulevel)(K:Type) := K⟶K; [∏_istype]($a, _ ⟾ $a, _ ⟾ _ ⟾ $a).

Check LF beta_reduction.

Check :

     [ |- T Type ] =>

     [ x : T |- U Type ] =>

     [ |- t : T ] =>

     [ x : T |- b : U ] =>

     [ (lambda x:T, b) t = t\\b : t\\U ].

End.

Check : 
	(T:(T0:texp) × (istype T0)) ⟶ 
	(U:(U0:texp) × (istype U0)) ⟶ 
	(t:(t0:oexp) × (hastype t0 (π₁ T))) ⟶ 
	(b:(b0:oexp) × (hastype b0 (π₁ U))) ⟶ 
	(oequal ([ev] ([λ] T (x ⟼ b)) t $ev3) (b t) (U t))
			      

should be

	(T:(T0:texp) × (istype T0)) ⟶ 
	(U:(U0:oexp -> texp) × (istype U0)) ⟶ 
	(t:(t0:oexp) × (hastype t0 (π₁ T))) ⟶ 
	(b:(b0:oexp -> oexp) × ((t':(t0:oexp) × (hastype t0 (π₁ T))) => (hastype ((π₁ b0) t') ((π₁ U) t')))) ⟶ 
	(oequal ([ev] ([λ] (π₁ T) (π₁ b)) (π₁ t) $ev3) ((π₁ b) (π₁ t)) ((π₁ U) (π₁ t)))

compare to

    beta_reduction : 

    	(T:texp) ⟶ 
	(U:oexp ⟶ texp) ⟶ 
	(t:oexp) ⟶ 
	(f:oexp ⟶ oexp) ⟶ 
	(hastype t T) ⟶ 
	((t':oexp) ⟶ (hastype t' T) ⟶ (hastype (f t') (U t'))) ⟶ 
	(oequal ([ev] ([λ] T f) t U) (f t) (U t))

End.

#   Local Variables:
#   compile-command: "make demo "
#   End:
