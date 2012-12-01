Variable u0 u1 u2 : Ulevel ; [next](u0) <= u1; [next](u1) < u2.
Variable T T' U V X Y : Type.
Axiom x0 : X.
Axiom f : T -> T.

Check Universes.

# Define A := T.
# Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Check lambda x:T, x.
Check T.
Check [El]([u](u2)).

# test LF term input format:
CheckLF (lambda x, ([ev] f x (lambda y, T))).

Check [U](u1).
Check [j](u1, u2).
Check *[u](u1).
Check max ([next](u1), u0).
Check [Sigma;x](T,T').
Check Sigma x:T, Sigma y:U, V -> X .
Check [Coprod](T,T').
# Check [Coprod;x,x'](T,T',U,U',[u](u0)).
Check [Empty]().
# Check lambda a:A, lambda q:B, lambda t:[IP;x,y,z](A,a,B,D,q), t.
Check lambda x:T, lambda y:T, lambda t:[Id](T,x,y), t.

Check lambda o:T, lambda o':T, [forall;x](u1,u2,o,o').

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

Check Pi x : T, [U]([next](u0)).
Check Pi x : T, [U](u0).

Check u1.
Check T.
Check lambda x:T, x.

Check lambda e:U, lambda x : T, e.

# ought to give a type checking error, and explain it well:
# Check lambda f:T -> T, f f.

Check lambda g:T -> [U](u1), lambda f:Pi t:T, *g t, lambda o:T, f o.

# ought to give a type checking error, and explain it well
# Check lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f f.

Check T -> U -> X -> Y.

Check lambda f:(X->X)->U, f lambda x:X, x.

Tau [u](u1).
Tau [j](u1,u2).
Tau [ev;x](f,x0,T).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,x0,x0).

Check lambda f:T->U, lambda o:T, [ev;_](f,o,U).
Check lambda f:T->U, lambda o:T, f o.
Check lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
Check lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
Check lambda f:X->T, lambda y:X, [ev;_](f,y,T).
Check lambda f:X->T, lambda y:X, f y.

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

CheckLFtype Pi x:oexp, Pi y:oexp, Pi T:texp, Pi U:texp, [ x = y : T ] -> [ T = U ] -> [ x = y : U ].
Check U_type.
CheckLF (U_type u1).

Define foo (u : Ulevel) (t : [U]([next](u))) := *t.
CheckLF ([foo.0] u1 ([u] u1) (u_univ u1)).
CheckLF ([foo.0] u1 ([u] u1) _).
