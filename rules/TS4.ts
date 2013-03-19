# -*- coding: utf-8 -*-

Include "rules/TS3.ts"..

# @empty, @empty_r, @Empty

Axiom 100 teq_empty_eta { ⊢ a : Empty, T T' Type } [ T ≡ T']..

Axiom 101 oeq_empty_eta { ⊢ a : Empty, T Type, o : T, o' : T } [ o ≡ o' : T ]..

Axiom 102 Empty_istype ⊢ Empty Type ..

#   Local Variables:
#   compile-command: "make -C .. rules4 "
#   End:
