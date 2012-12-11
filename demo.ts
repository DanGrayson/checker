# -*- coding: utf-8 -*-

# idea:
# Axiom LF car : Notation( (x |-> (pi1 x)) ).


Variable T : Type.

Check LFtype (T:texp) × (istype T) .
Axiom LF o : oexp.
Check LFtype oexp -> oexp.

Axiom t : T.

Define compose1 (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := [ev;_](g,[ev;_](f,t,U),V) : V ;; (
       # LF syntax
       ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) ($a) (ev_hastype T (_ ⟼ U) f t ($a) ($a))).

Define compose1' (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := [ev;_](g,[ev;_](f,t,U),V) : V ;
       # new TS syntax
       [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a)).

Define compose2 (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;;
      # LF syntax
      (λ_hastype T (_ ⟼ V) (t ⟼ ([ev] g ([ev] f t (_ ⟼ U)) (_ ⟼ V)) ) ($a) (t ⟼ _ ⟼ (ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) ($a) (ev_hastype T (_ ⟼ U) f t ($a) ($a) )))).

Define compose2' (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;
      # new TS syntax
      [λ_hastype](T, _ ⟾ V, t ⟾ g (f t), $a, t ⟾ _ ⟾ [ev_hastype](U, _ ⟾ V, g, f t, $a, [ev_hastype](T, _ ⟾ U, f, t, $a, $a))).


Define A (u : Ulevel; u=u) (t : [U](u)) := [El](t);; (El_type u ($a) ($0)).

Define A'(u : Ulevel; u=u) (t : [U](u)) := [El](t); [El_type](u, $a, $0).

Variable u1 : Ulevel.

Define C := [u](u1) : [U]([next](u1));; (u_univ ($a)).

Define B (u : Ulevel) (t : [U](u)) := [El](t);; (El_type u $a $0).

Check LF (B ([next] u1) ([u] u1) (u_univ u1)).

Check LF ∏_istype.

Define E (u1 u2 u3:Ulevel)(K:Type) := K⟶K;; (∏_istype ($a) (_ ⟼ ($a)) (_ ⟼ _ ⟼ ($a)) ).

Define E'(u1 u2 u3:Ulevel)(K:Type) := K⟶K; [∏_istype]($a, _ ⟾ $a, _ ⟾ _ ⟾ $a).

End.

Check LF beta_reduction.

Check LFtypeTS

     [ |- T Type ] =>

     [ x : T |- U Type ] =>

     [ |- t : T ] =>

     [ x : T |- b : U ] =>

     [ (lambda x:T, b) t = t\\b : t\\U ].   # here's where the error is

End.

Check :  (with sigma on)

	(T:(T0:texp) * (istype T0)) -> 
	(U:(U0:texp) * (istype U0)) -> 
	(t:(t0:oexp) * (hastype t0 (pi1 T))) -> 
	(b:(b0:oexp) * (hastype b0 (pi1 U))) -> 
	(oequal ([ev] ([λ] T (x ⟼ b)) t $ev3) (b t) (U t))

Check : (with sigma off)
	
	(T:texp) ⟶ (istype T) ⟶ 
	(U:texp) ⟶ (istype U) ⟶ 
	(t:oexp) ⟶ (hastype t T) ⟶ 
	(b:oexp) ⟶ (hastype b U) ⟶ 
	(oequal ([ev] ([λ] T (x ⟼ b)) t $ev3) (b t) (U t))

should be

	(T:(T0:texp) * (istype T0)) -> 
	(U:(U0:oexp -> texp) * (istype U0)) -> 
	(t:(t0:oexp) * (hastype t0 (pi1 T))) -> 
	(b:(b0:oexp -> oexp) * ((t':(t0:oexp) * (hastype t0 (pi1 T))) => (hastype ((pi1 b0) t') ((pi1 U) t')))) -> 
	(oequal ([ev] ([λ] (pi1 T) (pi1 b)) (pi1 t) $ev3) ((pi1 b) (pi1 t)) ((pi1 U) (pi1 t)))

compare to

    beta_reduction : 

    	(T:texp) -> 
	(U:oexp -> texp) -> 
	(t:oexp) -> 
	(f:oexp -> oexp) -> 
	(hastype t T) -> 
	((t':oexp) -> (hastype t' T) -> (hastype (f t') (U t'))) -> 
	(oequal ([ev] ([λ] T f) t U) (f t) (U t))

End.


#   Local Variables:
#   compile-command: "make demo "
#   End:
