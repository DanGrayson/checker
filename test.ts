# -*- coding: utf-8 -*-

Variable T : Type.
Define TT := T ;; $a.
Variable u0 u1 u2 : Ulevel ; [next](u0) <= u1; [next](u1) < u2.
Variable T' U V X Y : Type.
Axiom t0: T.
Axiom x0 : X.
Axiom f : T⟶T.
Check TS f t0.

Axiom 你好 : T⟶T.

Check Universes.

# Define A := T.
# Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Check TS λ x:T, x.
Check TS T.
Check TS [El]([u](u2)).

Check LF (λ x, ([ev] f x (λ y, T))).
Check LF (x⟼([ev] f x (λ y, T))).

Check TS [U](u1).
Check TS [j](u1, u2).
Check TS *[u](u1).
Check TS max ([next](u1), u0).
Check TS [Σ;x](T,T').
Check TS Σ x:T, Σ y:U, V⟶X .
Check TS [∐](T,T').
Check TS [Empty]().
Check TS λ x:T, λ y:T, λ t:[Id](T,x,y), t.

Check TS λ o:T, λ o':T, [∀;x](u1,u2,o,o').

Check TS ∏ x : T, [U]([next](u0)).
Check TS ∏ x : T, [U](u0).

Check TS u1.
Check TS T.
Check TS λ x:T, x.

Check TS λ e:U, λ x : T, e.

# ought to give a type checking error, and explain it well:
# Check TS λ f:T⟶T, f f.

Check TS lambda g:T⟶[U](u1), lambda f:∏ t:T, *g t, lambda o:T, f o.

# ought to give a type checking error, and explain it well
# Check TS λ g:T⟶*[u](u1), λ f:∏ t:T, *g t, λ o:T, f f.

Check TS T⟶U⟶X⟶Y.

Check TS λ f:(X⟶X)⟶U, f λ x:X, x.

Check TS [u](u1).
Check TS [j](u1,u2).
Check TS [ev;x](f,t0,T).
Check TS [λ;x](T,x).
Check TS [∀;x](u1,u2,x0,x0).

Check TS λ f:T⟶U, λ o:T, [ev;_](f,o,U).
Check TS λ f:T⟶U, λ o:T, f o.
Check TS λ k:U, λ g:T⟶*k, λ f:∏ t:T, *g t, λ o:T, f o.
Check TS λ r:U, λ f:T⟶U, λ o:T, λ x : *r, f o.
Check TS λ f:X⟶T, λ y:X, [ev;_](f,y,T).
Check TS λ f:X⟶T, λ y:X, f y.

Check TS U_type.
Check TS [Pi;x](T,T).

Check LFtype ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp, [ x = y : T ]⟶[ T = U ]⟶[ x = y : U ].
Check LF (U_type u1).

Check LF El_type.

Define foo (u : Ulevel) (t : [U]([next](u))) := *t;; (El_type ([next] u) t $a).

Define A (u : Ulevel) (t : [U](u)) := *t;; (El_type u t $a).

Define C (u : Ulevel) (t : [U](u)) := *t;; (El_type $2 $1 $0).

End.

Check LF ([A.0] ([next] u1) ([u] u1) (u_univ u1)).
Check LF ([A.1] ([next] u1) ([u] u1) (u_univ u1)).

Check LF type texp * oexp .
Check LF      pair ([U] u0) ([u] u0).
Check LF type Sigma x: uexp, texp.
Check LF      pair u0 ([U] u0).
Check LF type Singleton ( pair u0 ([U] u0) :  (Sigma x: uexp, texp) ).
# Show.


#   Local Variables:
#   compile-command: "make run "
#   End:
