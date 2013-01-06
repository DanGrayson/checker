# -*- coding: utf-8 -*-

Include "rules/TS5.ts".

# @[Id], @[paths], @[refl], @[J;x,e]

Axiom 11.5.1 paths_hastype { ⊢ M Ulevel, t : @[U](M), o1 o2 : @[El](t) } ⊢ @[paths](M,t,o1,o2) : @[U](M).

Axiom 11.5.2 Id_istype { ⊢ T Type, o1 o2 : T } ⊢ @[Id](T,o1,o2) Type.

Axiom 11.5.3 refl_hastype { ⊢ T Type, o : T } ⊢ @[refl](T,o) : @[Id](T,o,o).

Axiom 11.5.4 J_hastype { ⊢ T Type, a b:T, i:@[Id](T,a,b) } { x:T, e:@[Id](T,a,x) ⊢ S Type } { ⊢ q : S[a,@[refl](T,a)] } ⊢ @[J](T,a,b,q,i,S) : S[b,i].

#   Local Variables:
#   compile-command: "make -C .. rules6 "
#   End:
