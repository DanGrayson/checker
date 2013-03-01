# -*- coding: utf-8 -*-

Include "rules/TS1.ts".

# Pt, pt, tt

Axiom 5.3.1 Pt_istype ⊢ Pt Type.

Axiom 5.3.2 tt_hastype ⊢ tt : Pt.

Axiom 5.3.3 Pt_eta { ⊢ o : Pt } [ o ≡ tt : Pt ].

Axiom 5.3.4 pt_hastype ⊢ pt : UU[uu0].

Axiom 5.3.5 El_pt_reduction [ *pt ≡ Pt ].

Axiom 5.4.1 Pt_eliminator { ⊢ x : Pt } { t : Pt ⊢ T Type } { ⊢ o : T[tt] }

      ⊢ @[pt_r;t][o,T[t]] : ∏ x:Pt, T[x] .

#   Local Variables:
#   compile-command: "make -C .. rules2 "
#   End:
