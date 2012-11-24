# experiment with notation for rules and inferences.

Variable u0 u1 u2 : Ulevel ; u0+10 <= u1; u1+10 <= u2.
Variable T T' U V X Y : Type.
Check Universes.

Define A := T.
Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Show.

# Check lambda x:T, lambda y:U, [odef;foo](u1,u2;T,U;x,y).

Check lambda x:T, x.
Check T.
Check [El]([u](u2)).
Check [U](u1).
Check [j](u1, u2).
Check *[u](u1).
Check max (u1+1, u0).
Check [Sigma;x](T,T').
Check Sigma x:T, Sigma y:U, V -> X .
Check [Coprod](T,T').
# Check [Coprod;x,x'](T,T',U,U',[u](u0)).
Check [Empty]().
# Check lambda a:A, lambda q:B, lambda t:[IC;x,y,z](A,a,B,D,q), t.
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

Check Pi x : T, [U](u0+1).
Check Pi x : T, [U](u0).

Check u1.
Check T.
Check lambda x:T, x.
Show.

Check lambda e:U, lambda x : T, e.

Check lambda f:T -> T, f f.  # ought to give a type checking error, and explain it well

Check lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f o.

Check lambda g:T -> *[u](u1), lambda f:Pi t:T, *g t, lambda o:T, f f.  # ought to give a type checking error, and explain it well

Check T -> U -> X -> Y.

Check lambda f:(X->X)->U, f lambda x:X, x.

Tau [u](u4).
Tau [j](u,u').
Tau [j](_,u').
Tau [j](u,_).
Tau [ev;x](f,o,T).
Tau [ev;x](f,o, x).
Tau [lambda;x](T,x).
Tau [forall;x](u1,u2,o,o').

Define E1 (u:Ulevel)(K:Type)(x:K) := x : K.
Define E2 (u1 u2 u3:Ulevel)(K:Type) := K->K .
Define E3 (u1 u2 u3 : Ulevel)(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [U](u2) .
Define E5 (u1 u2 u3 : Ulevel; max (u1, u2) = max (u2, u3); u1 >= u2+1 )(K:Type)(x1: K -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : [U](u2) .
Define E7 (T U:Type)(t:T)(u:U)(f:T->U) := f t : _.
Define E7 (K L:Type)(t:K)(g:K -> [U](u0))(u:L)(f:Pi x:K, *g x) := f t : _.
Define E6 (u1 u2 u3 : Ulevel)(X1 X2:Type)(x1: X1 -> [U](u1))(x2: [U](u0+1)) := [j](x1, x2) : _ .

Check lambda f:T->U, lambda o:T, [ev;_](f,o,U).
Check lambda f:T->U, lambda o:T, f o.
Define E7 := ft : _ .
Check lambda k:U, lambda g:T -> *k, lambda f:Pi t:T, *g t, lambda o:T, f o.
Check lambda r:U, lambda f:T->U, lambda o:T, lambda x : *r, f o.
Check lambda f:X->T, lambda y:X, [ev;_](f,y,T).
Check lambda f:X->T, lambda y:X, f y.
# Check [udef;foo](u0+1,u1).
# Check lambda x:T, lambda y:U, lambda t:[tdef;foo](u0,u0;T,U;x,y), t.

# Check forall x:*y, z.	# fix the location of the holes

Show.
