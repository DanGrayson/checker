# Variable u0 : Ulevel.
Define E1 (u:Ulevel)(K:Type)(x:K) := x : K; $a.

# Define [E1.1] =  (u ⟼ K ⟼ i$2 ⟼ x ⟼ h$1 ⟼ $a)
#        [E1.1] => (u ⟼ K ⟼ i$2 ⟼ x ⟼ h$1 ⟼ h$1)
#        [E1.1] :  ∏ u:uexp, ∏ K:texp, ∏ i$2:(istype K), ∏ x:oexp, ∏ h$1:(hastype x K), (hastype ([E1.0] u K i$2 x h$1) K)
#        [E1.1] => ∏ u:uexp, ∏ K:texp, ∏ i$2:(istype K), ∏ x:oexp, ∏ h$1:(hastype x K), (hastype ([E1.0] u K i$2 x h$1) K)		OOPS

Show 100.
End.

# stuff below here doesn't work yet

Define E2 (u1 u2 u3:Ulevel)(K:Type) := K⟶K .
Define E3 (u1 u2 u3 : Ulevel)(K:Type)(x1: K ⟶ [U](u1))(x2: [U]([next](u0))) := [U](u2) .
Define E5 (u1 u2 u3 : Ulevel; max (u1, u2) = max (u2, u3); u1 >= [next](u2) )(K:Type)(x1: K ⟶ [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : [U](u2) .
Define E7 (T U:Type)(t:T)(u:U)(f:T ⟶ U) := f t : _.
Define E7 (K L:Type)(t:K)(g:K ⟶ [U](u0))(u:L)(f:∏ x:K, *g x) := f t : _.
Define E6 (u1 u2 u3 : Ulevel)(X1 X2:Type)(x1: X1 ⟶ [U](u1))(x2: [U]([next](u0))) := [j](x1, x2) : _ .

Define bar (T:Type) := T ⟶ T.
Define univ (u:Ulevel) := [U](u).

Define g1 := f : T ⟶ T.
Define g2 (T:Type) := λ x:T, x : T ⟶ T.
Define g3 (T:Type)(t:T) := λ x:T, t : T ⟶ T.

Variable u v : Ulevel ; u < v .
Axiom TS a : [Pt]().
Axiom LF T : texp.
Axiom LF i : (istype T).
Check Universes.



Define compose (T U V:Type) (f:T->U) (g:U->V) := lambda x:T, (g (f x)) : T->V.

#   Local Variables:
#   compile-command: "make run2 "
#   End:
