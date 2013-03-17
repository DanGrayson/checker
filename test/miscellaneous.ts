# -*- coding: utf-8 -*-

Include "rules/TS2.ts".

Variable T Type.

Theorem TT |- T Type ::= (pair _ _).
Variable u0 u1 u2 Ulevel ; next[u0] <= u1; next[u1] < u2.
Variable T' U V X Y Type.
Axiom t0: T.
Axiom x0 : X.
Axiom f : T⟶T.

Check LF x0.

# Check TS f t0.

Axiom 你好 : T⟶T.

Check Universes.

Axiom A |- T Type.

Check LF (λ x, (@[ev] f x T (λ y, T))).			    # two notations for the LF-lambda
Check LF (x ⟼ (@[ev] f x T (y ⟼ T))).

Check TS λ x:T, x.
Check TS T.
Check TS @[El][uu[u2]].
Check TS UU[u1].
Check TS jj[u1, u2].
Check TS *uu[u1].
Check TS max (next[u1], u0).
Check TS @[Σ;x][T,T'].
Check TS Σ x:T, Σ y:U, V⟶X .
Check TS @[∐][T,T'].
Check TS @[Empty][].
Check TS Empty.
Check TS λ x:T, λ y:T, λ t:@[Id][T,x,y], t.
Check TS λ o:T, λ o':T, @[forall;x][u1,u2,o,o'].
Check TS ∏ x : T, UU[next[u0]].
Check TS ∏ x : T, UU[u0].
Check TS u1.
Check TS T.
Check TS λ x:T, x.
Check TS λ e:U, λ x : T, e.

# ought to give a type checking error, and explain it well:
# Check TS λ f:T⟶T, f f.

# Check TS lambda g:T⟶UU[u1], lambda f:∏ t:T, *g t, lambda o:T, f o.

# ought to give a type checking error, and explain it well
# Check TS λ g:T⟶*uu[u1], λ f:∏ t:T, *g t, λ o:T, f f.

Check TS T⟶U⟶X⟶Y.

# Check TS λ f:(X⟶X)⟶U, f λ x:X, x.

Check TS uu[u1].
Check TS jj[u1,u2].
# Check TS @[ev;x][f,t0,T].
Check TS @[λ;x][T,x].
# Check TS @[forall;x][u1,u2,x0,x0].

Check TS λ f:T⟶U, λ o:T, @[ev;_][f,o,T,U].
# Check TS λ f:T⟶U, λ o:T, f o.
# Check TS λ k:U, λ g:T⟶*k, λ f:∏ t:T, *g t, λ o:T, f o.
# Check TS λ r:U, λ f:T⟶U, λ o:T, λ x : *r, f o.
Check TS λ f:X⟶T, λ y:X, @[ev;_][f,y,X,T].
# Check TS λ f:X⟶T, λ y:X, f y.

Check TS U_istype.
Check TS @[Pi;x][T,T].

Check LF : ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp, [ x ≡ y : T ]⟶[ T ≡ U ]⟶[ x ≡ y : U ].
Check LF (U_istype u1).

Check LF El_istype.

Theorem foo { ⊢ u Ulevel, t : UU[next[u]] } ⊢ *t Type ::= u |-> t |-> (El_istype (next u) t).

Theorem fot { ⊢ u Ulevel, t : UU[next[u]] } ⊢ *t Type ::= u |-> t |-> (El_istype (next u) t).

Theorem B   { ⊢ u Ulevel, t : UU[u        ] } ⊢ *t Type ::= u |-> t |-> (El_istype u t).

Check LF : texp ** oexp .
Check LF      (pair (UU u0) (uu u0)).
Check LF : Sigma x: uexp, texp.
Check LF      (pair u0 (UU u0)).
Check LF : Singleton ( (pair u0 (UU u0)) :  (Sigma x: uexp, texp) ).
# Show.


#   Local Variables:
#   compile-command: "make -C .. miscellaneous "
#   End:
