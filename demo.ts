# -*- coding: utf-8 -*-

Check : [ |- T Type ] => texp.

Rule 27 beta_reduction :

     [ |- T Type ] =>

     [ x : T |- U Type ] =>

     [ |- t : T ] =>

     [ x : T |- b : U ] =>

     [ (lambda x:T, b) t = t\\b : t\\U ].

End.

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

End.

#   Local Variables:
#   compile-command: "make demo "
#   End:
