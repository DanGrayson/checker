# -*- coding: utf-8 -*-

Axiom 200 jMM_reduction { ⊢ M1 M2 Ulevel } [ M1 ~ M2 Ulevel ] ⇒ [ @[j](M1,M2) ≡ @[λ;x](@[U](M1),x) : @[U](M1) -> @[U](M2) ].

Axiom 201 jj_reduction { ⊢ M1 M2 M2' M3 Ulevel, o : @[U](M1) }
		
		[ M2 ~ M2' Ulevel ] ⇒ [  @[j](M2',M3) (@[j](M1,M2) o) ≡  @[j](M1,M3) o : @[U](M1) -> @[U](M3) ].

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
