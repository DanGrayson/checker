# -*- coding: utf-8 -*-

Axiom 102 Empty ⊢ [Empty]() Type .

Axiom 100 teq_empty_eta { ⊢ a : [Empty](), T T' Type } [ T = T'].

Axiom 101 oeq_empty_eta { ⊢ a : [Empty](), T Type, o : T, o' : T } [ o = o' : T ].

Axiom 200 jMM_reduction { ⊢ M1 M2 Ulevel } [ M1 ~ M2 Ulevel ] ⇒ [ [j](M1,M2) = [λ;x]([U](M1),x) : [U](M1) -> [U](M2) ].

Axiom 201 jj_reduction { ⊢ M1 M2 M2' M3 Ulevel, o : [U](M1) }
		
		[ M2 ~ M2' Ulevel ] ⇒ [  [j](M2',M3) ([j](M1,M2) o) =  [j](M1,M3) o : [U](M1) -> [U](M3) ].
