# -*- coding: utf-8 -*-

Axiom 200 jMM_reduction { ⊢ M1 M2 Ulevel } [ M1 ~ M2 Ulevel ] ⇒ [ @[j][M1,M2] ≡ @[λ;x][UU[M1],x] : UU[M1] -> UU[M2] ].

Axiom 201 jj_reduction { ⊢ M1 M2 M2' M3 Ulevel, o : UU[M1] }
		
		[ M2 ~ M2' Ulevel ] ⇒ [  @[j][M2',M3] (@[j][M1,M2] o) ≡  @[j][M1,M3] o : UU[M1] -> UU[M3] ].

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
