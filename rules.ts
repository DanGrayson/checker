# -*- coding: utf-8 -*-

# the derivation rules for TS0

Variable uu0 Ulevel.

Rule 3.4.7 tsimeq { ⊢ T U Type } [ T ~ U Type ] ⇒ [ T = U ].

Rule 3.4.8 teqsymm { ⊢ T U Type } [ U = T ] ⇒ [ T = U ].

Rule 3.4.9 teqtrans { ⊢ T U V Type } [ T = U ] ⇒ [ U = V ] ⇒ [ T = V ].

Rule 3.4.10 osimeq { ⊢ T Type, x y : T } [ x ~ y ] ⇒ [ x = y : T ].

Rule 3.4.11 oeqsymm { ⊢ T Type, x : T, y : T } [ x = y : T ] ⇒ [ y = x : T ].

Rule 3.4.12 oeqtrans { ⊢ T Type, x : T, y : T, z : T } [ x = y : T ] ⇒ [ y = z : T ] ⇒ [ x = z : T ].

Rule 3.4.13 cast { ⊢ T U Type, o : T } [ T = U ] ⇒ [ o : U ].

Rule 3.4.14 oeqcast { ⊢ T U Type, x : T, y : T } [ x = y : T ] ⇒ [ T = U ] ⇒ [ x = y : U ].

Rule 3.4.15 U_istype { ⊢ M Ulevel } ⊢ [U](M) Type.

Rule 3.4.16 u_hastype { ⊢ M Ulevel } ⊢ [u](M) : [U]([next](M)).

Rule 3.4.17 El_istype { ⊢ M Ulevel, o : [U](M) } ⊢ *o Type.

Rule 3.4.18 El_u_reduction { ⊢ M Ulevel } [ *[u](M) = [U](M) ].

Rule 3.4.19 El_eq { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ x = y : [U](M) ] ⇒ [ *x = *y ].

Rule 3.4.20 El_eq_reflect { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ *x = *y ] ⇒ [ x = y : [U](M) ].

Rule 3.4.21 ∏_istype { ⊢ T Type } { _ : T ⊢ U Type } ⊢ [∏](T,U) Type .

Rule 3.4.22 ∏_eq { ⊢ T T' Type } { _ : T ⊢ U U' Type } [ T = T' ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒ [ [∏](T,U) = [∏](T',U') ].

Rule 3.4.22.1 ∏_eq1 { ⊢ T T' Type } { _ : T ⊢ U Type } [ T = T' ] ⇒ [ [∏](T,U) = [∏](T',U) ].

Rule 3.4.22.2 ∏_eq2 { ⊢ T Type } { _ : T ⊢ U U' Type } ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒ [ [∏](T,U) = [∏](T,U') ].

Rule 3.4.23 λ_hastype { ⊢ T Type } { _ : T ⊢ U Type } { x : T ⊢ o : U/x } ⊢ [λ](T,o) : [∏](T,U).

Rule 3.4.24 λ_equality { ⊢ T T' Type } { _ : T ⊢ U U' Type } { x : T ⊢ o o' : U/x }

     			[ T = T' ] ⇒ ( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T',o') : [∏](T,U) ].

Rule 3.4.24.1 λ_equality1 { ⊢ T T' Type } { x : T ⊢ U Type, o : U/x }

     			[ [λ](T,o) = [λ](T',o) : [∏](T,U) ].

Rule 3.4.24.2 λ_equality2 { ⊢ T Type } { x : T ⊢ U U' Type, o o' : U/x } 

     			( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T,o') : [∏](T,U) ].

Rule 3.4.25 ev_hastype { ⊢ T Type } { _ : T ⊢ U Type } { ⊢ f : [∏](T,U), o : T } ⊢ f o : U/o.

Rule 3.4.25.1 ev { ⊢ T U Type, f : T -> U, o : T } ⊢ f o : U.  # non-dependent version

Rule 3.4.26 ev_eq { ⊢ T Type, o o' : T } { _ : T ⊢ U U' Type } { ⊢ f f' : [∏](T,U) } 

	      [ f = f' : [∏](T,U) ] ⇒ [ o = o' : T ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒

	      [ [ev](f,o,U) = [ev](f',o',U') : U/o ].

# should make it possible to omit third branch of U here:

Rule 3.4.27 beta_reduction { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U/x } [ [ev]([λ](T,o2),o1,U) = o2/o1 : U/o1 ].

Rule 3.4.28 eta_reduction { ⊢ T Type } { _ : T ⊢ U Type } { ⊢ f : [∏](T,U) } [ [λ;x](T,[ev](f,x,U)) = f : [∏](T,U) ].

Rule 3.4.29 j_type { ⊢ M1 M2 Ulevel } [ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ [j](M1,M2) : [U](M1) -> [U](M2) ].

Rule 3.4.30 El_j_reduction { ⊢ M1 M2 Ulevel, o : [U](M1) } 

     		[ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ *[ev;_]([j](M1,M2),o,[U](M2)) = *o ].

Rule 3.4.31 forall { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { x : *o1 ⊢ o2 : [U](M2) } ⊢ [∀](M1,M2,o1,o2) : [U]([max](M1,M2)).

Rule 3.4.32 El_forall_reduction { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { _ : *o1 ⊢ o2 : [U](M2) }

          [ (*[∀](M1,M2,o1,o2)) = ([∏;x](*o1,[El](o2/x))) ].		# parser doesn't let us use *(o2/x); fix

Rule 5.3.1 Pt_istype ⊢ [Pt]() Type. 

Rule 5.3.2 tt_hastype ⊢ [tt]() : [Pt](). 

Rule 5.3.3 Pt_eta { ⊢ o : [Pt]() } [ o = [tt]() : [Pt]() ].

Rule 5.3.4 pt_hastype ⊢ [pt]() : [U](uu0).

Rule 5.3.5 El_pt_reduction [ [El]([pt]()) = [Pt]() ].

Rule 5.4.1 Pt_eliminator { ⊢ x : [Pt]() } { _ : [Pt]() ⊢ T Type } { ⊢ o : T/[tt]() } ⊢ [pt_r](o,T) : [Pi;x]([Pt](),T/x) .

Rule 102 Empty ⊢ [Empty]() Type .

Rule 100 teq_empty_eta { ⊢ a : [Empty](), T T' Type } [ T = T'].

Rule 101 oeq_empty_eta { ⊢ a : [Empty](), T Type, o : T, o' : T } [ o = o' : T ].

Rule 200 jMM_reduction { ⊢ M1 M2 Ulevel } [ M1 ~ M2 Ulevel ] ⇒ [ [j](M1,M2) = [λ;x]([U](M1),x) : [U](M1) -> [U](M2) ].

Rule 201 jj_reduction { ⊢ M1 M2 M2' M3 Ulevel, o : [U](M1) }
		
		[ M2 ~ M2' Ulevel ] ⇒ [  [j](M2',M3) ([j](M1,M2) o) =  [j](M1,M3) o : [U](M1) -> [U](M3) ].


#   Local Variables:
#   compile-command: "make rules "
#   End:
