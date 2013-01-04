# -*- coding: utf-8 -*-

Include "rules/TS0.ts".

# Sigma, pair, pr1, pr2, total

Axiom 6.3.1 Σ_istype { ⊢ T Type } { t : T ⊢ U Type } ⊢ [Σ;t](T,U/t) Type .

Axiom 6.3.2 pair_hastype { ⊢ T1 Type } { x : T1 ⊢ T2 Type } { ⊢ o1 : T1, o2 : T2/o1 } ⊢ [pair;x](o1,o2,T2/x) : [Σ;x](T1,T2/x).

#   Local Variables:
#   compile-command: "make -C .. rules1 "
#   End:
