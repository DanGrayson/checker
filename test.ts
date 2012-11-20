# experiment with notation for rule and inferences.

Variable u0 u1 u2 : Ulevel ; u0+10 <= u1; u1+10 <= u2.
Check Universes.

Variable T T' U V X Y : Type.

Define type A := T.
Define a := x : X.
Define equality e := x == y : X.
Define type equality e := X == Y.

Show.

# Check lambda x:T, lambda y:U, [odef;foo](u1,u2;T,U;x,y).

Check lambda x:T, x.
Check type T.
Check type [El]([u](u2)).
Check type [U](u4).
Check [j](u1, u2).
Check type *[u](u1).
Check ulevel max (u1+1, u0).
Check type [Sigma;x](T,T').
Check type Sigma x:T, Sigma y:U, V -> X .
Check type [Coprod](T,T').
# Check type [Coprod;x,x'](T,T',U,U',[u](u0)).
Check type [Empty]().
# Check lambda a:A, lambda q:B, lambda t:[IC;x,y,z](A,a,B,D,q), t.
Check lambda x:T, lambda y:T, lambda t:[Id](T,x,y), t.

Check lambda o:T, lambda o':T, [forall;x](u1,u2,o,o').

tAlpha Pi x:T, U  ==  Pi y:T, U .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:Pi a:T, U, lambda x:T, g x
   ==  lambda h:Pi b:T, U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g a
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h b  .
oAlpha lambda g:T->U, lambda x:T, g h
   ==  lambda h:T->U, lambda y:T, h y  .
oAlpha lambda g:T->U, lambda x:T, g x
   ==  lambda h:T->U, lambda y:T, h h  .

Check type Pi x : T, [U](u0+1).
Check type Pi x : T, [U](u0).

Check ulevel u1.
Check type T.
Check lambda x:T, x.
Show.

Check lambda e:U, lambda x : T, e.

Check lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f o.

Check type T -> U -> X -> Y.

Check lambda f:(X->X)->U, f lambda x:X, x.

Tau 14.
Tau [u](u4).
Tau [j](u,u').
Tau [j](_,u').
Tau [j](u,_).
Tau [ev;x](f,o,T).
Tau [ev;x](f,o, x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

Define E1 (u:Ulevel)(K:Type)(x:K) := x : K.
Define type E2 (u1 u2 u3:Ulevel)(K:Type) := K->K .
Define type E3 (u1 u2 u3 : Ulevel)(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [U](u2) .
Define E5 (u1 u2 u3 : Ulevel; max (u1, u2) = max (u2, u3); u1 >= u2+1 )(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : [U](u2) .
Define E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t : _.
Define E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K, *g x) := f t : _.
Define E6 (u1 u2 u3 : Ulevel)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : _ .

Check lambda f:T->U, lambda o:T, [ev;_](f,o,U).
Check lambda f:T->U, lambda o:T, f x.
Check lambda f:T->U, lambda o:T, f o.
Define E7 := ft : _ .
Check lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
Check lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
Check lambda f:X->T, lambda y:X, [ev;_](f,y,T).
Check lambda f:X->T, lambda y:X, f y.
# Check ulevel [udef;foo](u0+1,u1).
# Check lambda x:T, lambda y:U, lambda t:[tdef;foo](u0,u0;T,U;x,y), t.
Check lambda t:[U](u0), lambda f: *(lambda x:[U](u0), x) t -> U, lambda o:*t, f o.

# Check forall x:*y, z.	# fix the location of the holes
