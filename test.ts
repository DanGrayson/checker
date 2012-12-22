# -*- coding: utf-8 -*-

Variable T Type.
Theorem TT |- T Type ;; (pair _ _).
Variable u0 u1 u2 Ulevel ; [next](u0) <= u1; [next](u1) < u2.
Variable T' U V X Y Type.
Rule t0: T.
Rule x0 : X.
Rule f : T⟶T.

Check LF x0.

# Check TS f t0.

Rule 你好 : T⟶T.

Check Universes.

Rule A |- T Type.

Check LF (λ x, ([ev] f x (λ y, T))).
Check LF (x⟼([ev] f x (λ y, T))).

Check TS λ x:T, x.
Check TS T.
Check TS [El]([u](u2)).
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

# Check TS lambda g:T⟶[U](u1), lambda f:∏ t:T, *g t, lambda o:T, f o.

# ought to give a type checking error, and explain it well
# Check TS λ g:T⟶*[u](u1), λ f:∏ t:T, *g t, λ o:T, f f.

Check TS T⟶U⟶X⟶Y.

# Check TS λ f:(X⟶X)⟶U, f λ x:X, x.

Check TS [u](u1).
Check TS [j](u1,u2).
# Check TS [ev;x](f,t0,T).
Check TS [λ;x](T,x).
# Check TS [∀;x](u1,u2,x0,x0).

Check TS λ f:T⟶U, λ o:T, [ev;_](f,o,U).
# Check TS λ f:T⟶U, λ o:T, f o.
# Check TS λ k:U, λ g:T⟶*k, λ f:∏ t:T, *g t, λ o:T, f o.
# Check TS λ r:U, λ f:T⟶U, λ o:T, λ x : *r, f o.
Check TS λ f:X⟶T, λ y:X, [ev;_](f,y,T).
# Check TS λ f:X⟶T, λ y:X, f y.

Check TS U_istype.
Check TS [Pi;x](T,T).

Check : LF ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp, [ x = y : T ]⟶[ T = U ]⟶[ x = y : U ].
Check LF (U_istype u1).

Check LF El_istype.

Theorem foo { ⊢ u Ulevel, t : [U]([next](u)) } ⊢ *t Type ;; u |-> t |-> (El_istype ([next] u) t).

Theorem fot { ⊢ u Ulevel, t : [U]([next](u)) } ⊢ *t Type ;; u |-> t |-> (El_istype ([next] u) t).

Theorem B   { ⊢ u Ulevel, t : [U](u        ) } ⊢ *t Type ;; u |-> t |-> (El_istype u t).

Theorem C { ⊢ u Ulevel, t : [U](u) } ⊢ *t Type ;; u |-> t |-> (El_istype $1 $0).

Check : LF texp ** oexp .
Check LF      (pair ([U] u0) ([u] u0)).
Check : LF Sigma x: uexp, texp.
Check LF      (pair u0 ([U] u0)).
Check : LF Singleton ( (pair u0 ([U] u0)) :  (Sigma x: uexp, texp) ).
# Show.


#   Local Variables:
#   compile-command: "make run "
#   End:
