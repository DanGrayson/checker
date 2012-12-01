# -*- coding: utf-8 -*-

Variable T : Type.
Show.
Define TT := T ; (ist$1).

Variable u0 u1 u2 : Ulevel ; [next](u0) <= u1; [next](u1) < u2.
Variable T' U V X Y : Type.
Axiom t0: T.
Axiom x0 : X.
Axiom f : T ⟶ T.

Axiom 你好 : T ⟶ T.

Check Universes.

# Define A := T.
# Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Check TS λ x:T, x.
Check TS T.
Check TS [El]([u](u2)).

Check LF (λ x, ([ev] f x (λ y, T))).
Check LF (x ⟼ ([ev] f x (λ y, T))).

Check TS [U](u1).
Check TS [j](u1, u2).
Check TS *[u](u1).
Check TS max ([next](u1), u0).
Check TS [Σ;x](T,T').
Check TS Σ x:T, Σ y:U, V ⟶ X .
Check TS [∐](T,T').
Check TS [Empty]().
Check TS λ x:T, λ y:T, λ t:[Id](T,x,y), t.

Check TS λ o:T, λ o':T, [∀;x](u1,u2,o,o').

Alpha ∏ x:T, U  ==  ∏ y:T, U .
Alpha λ g:T ⟶ U, λ x:T, g x
  ==  λ h:T ⟶ U, λ y:T, h y  .
Alpha λ g:∏ a:T, U, λ x:T, g x
  ==  λ h:∏ b:T, U, λ y:T, h y  .
Alpha λ g:T ⟶ U, λ x:T, g a
  ==  λ h:T ⟶ U, λ y:T, h y  .
Alpha λ g:T ⟶ U, λ x:T, g x
  ==  λ h:T ⟶ U, λ y:T, h b  .
Alpha λ g:T ⟶ U, λ x:T, g h
  ==  λ h:T ⟶ U, λ y:T, h y  .
Alpha λ g:T ⟶ U, λ x:T, g x
  ==  λ h:T ⟶ U, λ y:T, h h  .

Check TS ∏ x : T, [U]([next](u0)).
Check TS ∏ x : T, [U](u0).

Check TS u1.
Check TS T.
Check TS λ x:T, x.

Check TS λ e:U, λ x : T, e.

# ought to give a type checking error, and explain it well:
# Check TS λ f:T ⟶ T, f f.

Check TS λ g:T ⟶ [U](u1), λ f:∏ t:T, *g t, λ o:T, f o.

# ought to give a type checking error, and explain it well
# Check TS λ g:T ⟶ *[u](u1), λ f:∏ t:T, *g t, λ o:T, f f.

Check TS T ⟶ U ⟶ X ⟶ Y.

Check TS λ f:(X ⟶ X) ⟶ U, f λ x:X, x.

Check TS [u](u1).
Check TS [j](u1,u2).
Check TS [ev;x](f,t0,T).
Check TS [λ;x](T,x).
Check TS [∀;x](u1,u2,x0,x0).

Check TS λ f:T ⟶ U, λ o:T, [ev;_](f,o,U).
Check TS λ f:T ⟶ U, λ o:T, f o.
Check TS λ k:U, λ g:T ⟶ *k, λ f:∏ t:T, *g t, λ o:T, f o.
Check TS λ r:U, λ f:T ⟶ U, λ o:T, λ x : *r, f o.
Check TS λ f:X ⟶ T, λ y:X, [ev;_](f,y,T).
Check TS λ f:X ⟶ T, λ y:X, f y.

# Define E1 (u:Ulevel)(K:Type)(x:K) := x : K.
# Define E2 (u1 u2 u3:Ulevel)(K:Type) := K⟶K .
# Define E3 (u1 u2 u3 : Ulevel)(K:Type)(x1: K ⟶ [U](u1))(x2: [U]([next](u0))) := [U](u2) .
# Define E5 (u1 u2 u3 : Ulevel; max (u1, u2) = max (u2, u3); u1 >= [next](u2) )(K:Type)(x1: K ⟶ [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : [U](u2) .
# Define E7 (T U:Type)(t:T)(u:U)(f:T ⟶ U) := f t : _.
# Define E7 (K L:Type)(t:K)(g:K ⟶ [U](u0))(u:L)(f:∏ x:K, *g x) := f t : _.
# Define E6 (u1 u2 u3 : Ulevel)(X1 X2:Type)(x1: X1 ⟶ [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : _ .

# Define bar (T:Type) := T ⟶ T.
# Define univ (u:Ulevel) := [U](u).
# 
# Define g1 := f : T ⟶ T.
# Define g2 (T:Type) := λ x:T, x : T ⟶ T.
# Define g3 (T:Type)(t:T) := λ x:T, t : T ⟶ T.

Check LF type ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp, [ x = y : T ] ⟶ [ T = U ] ⟶ [ x = y : U ].
Check TS U_type.
Check LF (U_type u1).

Define foo (u : Ulevel) (t : [U]([next](u))) := *t; _.
Check LF ([foo.0] u1 ([u] u1) (u_univ u1)).
Check LF ([foo.0] u1 ([u] u1) _).
