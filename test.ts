Variable u0 u1 u2 : Ulevel ; [next](u0) <= u1; [next](u1) < u2.
Variable T T' U V X Y : Type.
Axiom t0: T.
Axiom x0 : X.
Axiom f : T -> T.

Check Universes.

# Define A := T.
# Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Check TS lambda x:T, x.
Check TS T.
Check TS [El]([u](u2)).

Check LF (lambda x, ([ev] f x (lambda y, T))).

Check TS [U](u1).
Check TS [j](u1, u2).
Check TS *[u](u1).
Check TS max ([next](u1), u0).
Check TS [Sigma;x](T,T').
Check TS Sigma x:T, Sigma y:U, V -> X .
Check TS [Coprod](T,T').
Check TS [Empty]().
Check TS lambda x:T, lambda y:T, lambda t:[Id](T,x,y), t.

Check TS lambda o:T, lambda o':T, [forall;x](u1,u2,o,o').

Alpha Pi x:T, U  ==  Pi y:T, U .
Alpha lambda g:T->U, lambda x:T, g x
  ==  lambda h:T->U, lambda y:T, h y  .
Alpha lambda g:Pi a:T, U, lambda x:T, g x
  ==  lambda h:Pi b:T, U, lambda y:T, h y  .
Alpha lambda g:T->U, lambda x:T, g a
  ==  lambda h:T->U, lambda y:T, h y  .
Alpha lambda g:T->U, lambda x:T, g x
  ==  lambda h:T->U, lambda y:T, h b  .
Alpha lambda g:T->U, lambda x:T, g h
  ==  lambda h:T->U, lambda y:T, h y  .
Alpha lambda g:T->U, lambda x:T, g x
  ==  lambda h:T->U, lambda y:T, h h  .

Check TS Pi x : T, [U]([next](u0)).
Check TS Pi x : T, [U](u0).

Check TS u1.
Check TS T.
Check TS lambda x:T, x.

Check TS lambda e:U, lambda x : T, e.

# ought to give a type checking error, and explain it well:
# Check TS lambda f:T -> T, f f.

Check TS lambda g:T -> [U](u1), lambda f:Pi t:T, *g t, lambda o:T, f o.

# ought to give a type checking error, and explain it well
# Check TS lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f f.

Check TS T -> U -> X -> Y.

Check TS lambda f:(X->X)->U, f lambda x:X, x.

Check TS [u](u1).
Check TS [j](u1,u2).
Check TS [ev;x](f,t0,T).
Check TS [lambda;x](T,x).
Check TS [forall;x](u1,u2,x0,x0).

Check TS lambda f:T->U, lambda o:T, [ev;_](f,o,U).
Check TS lambda f:T->U, lambda o:T, f o.
Check TS lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
Check TS lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
Check TS lambda f:X->T, lambda y:X, [ev;_](f,y,T).
Check TS lambda f:X->T, lambda y:X, f y.

# Define E1 (u:Ulevel)(K:Type)(x:K) := x : K.
# Define E2 (u1 u2 u3:Ulevel)(K:Type) := K->K .
# Define E3 (u1 u2 u3 : Ulevel)(K:Type)(x1: K -> [U](u1))(x2: [U]([next](u0))) := [U](u2) .
# Define E5 (u1 u2 u3 : Ulevel; max (u1, u2) = max (u2, u3); u1 >= [next](u2) )(K:Type)(x1: K -> [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : [U](u2) .
# Define E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t : _.
# Define E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K, *g x) := f t : _.
# Define E6 (u1 u2 u3 : Ulevel)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : _ .

# Define bar (T:Type) := T -> T.
# Define univ (u:Ulevel) := [U](u).
# 
# Define g1 := f : T -> T.
# Define g2 (T:Type) := lambda x:T, x : T -> T.
# Define g3 (T:Type)(t:T) := lambda x:T, t : T -> T.

Check LF type Pi x:oexp, Pi y:oexp, Pi T:texp, Pi U:texp, [ x = y : T ] -> [ T = U ] -> [ x = y : U ].
Check TS U_type.
Check LF (U_type u1).

Define foo (u : Ulevel) (t : [U]([next](u))) := *t.
Check LF ([foo.0] u1 ([u] u1) (u_univ u1)).
Check LF ([foo.0] u1 ([u] u1) _).
