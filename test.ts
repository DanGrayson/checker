# experiment with notation for rules and inferences.

Rule 7 tsimeq :

     Pi T:texp, Pi U:texp,
     [ T ~ U ] -> [ T = U ].

Rule 8 teqsymm :

     Pi T:texp, Pi U:texp,
     [ T = U ] -> [ U = T ].

Rule 9 teqtrans :

     Pi T:texp, Pi U:texp, Pi V:texp,
     [ T = U ] -> [ U = V ] -> [ T = V ].

Rule 10 osimeq :

     Pi x:oexp, Pi y:oexp, Pi T:texp,
     [ x ~ y : T ] -> [ x = y : T ].

Rule 11 oeqsymm :

     Pi x:oexp, Pi y:oexp, Pi T:texp,
     [ x = y : T ] -> [ y = x : T ].

Rule 12 oeqtrans :

     Pi x:oexp, Pi y:oexp, Pi z:oexp, Pi T:texp,
     [ x = y : T ] -> [ y = z : T ] -> [ x = z : T ].

Rule 13 cast :

     Pi o:oexp, Pi T:texp, Pi U:texp,
     [ o : T ] -> [ T = U ] -> [ o : U  ].

Rule 14 oeqcast :

     Pi x:oexp, Pi y:oexp, Pi T:texp, Pi U:texp,
     [ x = y : T ] -> [ T = U ] -> [ x = y : U ].

Rule 15 U_type :

     Pi M:uexp, 
     [ ([U] M) type ].

# Rule 16 u_univ :
# 
#      Pi M:uexp,
#      [ [u] M : [U] ([plus;1] M) ].

Rule 17 El_type :

     Pi M:uexp, Pi o:oexp,
     [ o : [U] M ] -> [ [El] o type ].

Rule 18 El_u_univ :

     Pi M:uexp,
     [ [El]([u] M) = [U] M ].

Rule 19 El_eq :

     Pi M:uexp, Pi x:oexp, Pi y:oexp, 
     [ x = y : [U] M ] -> [ [El] x = [El] y ].

Rule 20 El_eq_reflect :

     Pi M:uexp, Pi x:oexp, Pi y:oexp, 
     [ x : [U] M ] -> [ y : [U] M ] -> [ [El] x = [El] y ] -> [ x = y : [U] M ].

Rule 21 Pi_istype :

     Pi T:texp, Pi x:oexp, Pi U:oexp -> texp, Pi y:oexp,
     [ x : T ] -> [ y : U x ] -> [ [Pi] T U type ].

Rule 25 hastype_ev : 

     Pi T : texp, Pi U : oexp -> texp, Pi g : oexp, Pi x : oexp,
     [ g : [forall] T U ] -> [ x : T ] -> [ [ev] g x U : U x].

Rule 32 type_El_forall :

     Pi M_1 : uexp, Pi M_2 : uexp, Pi o_1 : oexp, Pi o_2 : oexp -> oexp,
     [ o_1 : [U] M_1 ] ->
     (Pi x: oexp, [ x : [El] o_1 ] -> [ o_2 : [U] M_2 ])
     ->
     [ [El] ([forall] M_1 M_2 o_1 o_2) = [Pi] ([El] o_1) (lambda x, ([El] (o_2 x))) ].

Variable u0 u1 u2 : Ulevel ; u0+10 <= u1; u1+10 <= u2.
Variable T T' U V X Y : Type.
Check Universes.

Define A := T.
Define a := x : X.
# Define e := x == y : X.
# Define e := X == Y.

Show.

Check lambda x:T, lambda y:U, [foo.0](u1,u2,T,U,x,y).

Check lambda x:T, x.
Check T.
Check [El]([u](u2)).

# test lf-expr input format:
Print (lambda x, ([ev] f x (lambda y, T))).

F_Print Pi u1:uexp, Pi u2:uexp, Pi T:texp, Pi t:oexp, Pi ist:istype T, Pi has:hastype t T, texp.

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
Check [foo.0](u0+1,u1).
Check lambda x:T, lambda y:U, lambda t:[foo.1](u0,u0,T,U,x,y), t.

Define foo1 (u1 u2 : Ulevel) (T : Type) (t : T) := *t.

Show.
