# -*- coding: utf-8 -*-

Include "rules/TS0.ts"..

# Sigma, pair, pr1, pr2, total

Axiom 6.3.1 Σ_istype { ⊢ T Type } { t : T ⊢ U Type }

       ⊢ Σ t:T, U[t] Type ..

Axiom 6.3.2 pair_hastype { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] }

       ⊢ @pair[o1,o2,T2] : Σ x:T1, T2[x]..

Axiom 6.3.3 pr1_hastype { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] }

       ⊢ @pr1[T1,T2,a] : T1..

Axiom 6.3.4 pr2_hastype { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] }

       ⊢ @pr2[T1,T2,a] : T2[@pr1[T1,T2,a]]..

Axiom 6.3.5 pr1_pair_reduction { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] }

        [ @pr1[T1,T2,@pair[o1,o2,T2]] ≡ o1 : T1 ]..

Axiom 6.3.6 pr2_pair_reduction { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2[o1] }

        [ @pr2[T1,T2,@pair[o1,o2,T2]] ≡ o2 : T2[o1] ]..

Axiom 6.3.7 pair_eta_reduction { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ a : Σ x:T1, T2[x] }

      	[ @pair[@pr1[T1,T2,a],@pr2[T1,T2,a],T2] ≡ a : Σ x:T1, T2[x] ]..

# ....

#   Local Variables:
#   compile-command: "make -C .. rules1 "
#   End:
