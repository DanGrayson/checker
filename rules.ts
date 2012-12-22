# -*- coding: utf-8 -*-

# the derivation rules for TS0

Variable uu0 Ulevel.

Axiom 3.4.7 tsimeq { ⊢ T U Type } [ T ~ U Type ] ⇒ [ T = U ].

Axiom 3.4.8 teqsymm { ⊢ T U Type } [ U = T ] ⇒ [ T = U ].

Axiom 3.4.9 teqtrans { ⊢ T U V Type } [ T = U ] ⇒ [ U = V ] ⇒ [ T = V ].

Axiom 3.4.10 osimeq { ⊢ T Type, x y : T } [ x ~ y ] ⇒ [ x = y : T ].

Axiom 3.4.11 oeqsymm { ⊢ T Type, x : T, y : T } [ x = y : T ] ⇒ [ y = x : T ].

Axiom 3.4.12 oeqtrans { ⊢ T Type, x : T, y : T, z : T } [ x = y : T ] ⇒ [ y = z : T ] ⇒ [ x = z : T ].

Axiom 3.4.13 cast { ⊢ T U Type } [ T = U ] ⇒ { ⊢ o : T } ⊢ o : U.

Axiom 3.4.14 oeqcast { ⊢ T U Type, x : T, y : T } [ x = y : T ] ⇒ [ T = U ] ⇒ [ x = y : U ].

Axiom 3.4.15 U_istype { ⊢ M Ulevel } ⊢ [U](M) Type.

Axiom 3.4.16 u_hastype { ⊢ M Ulevel } ⊢ [u](M) : [U]([next](M)).

Axiom 3.4.17 El { ⊢ M Ulevel, o : [U](M) } ⊢ *o Type.

Axiom 3.4.18 El_u_reduction { ⊢ M Ulevel } [ *[u](M) = [U](M) ].

Axiom 3.4.19 El_eq { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ x = y : [U](M) ] ⇒ [ *x = *y ].

Axiom 3.4.20 El_eq_reflect { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ *x = *y ] ⇒ [ x = y : [U](M) ].

Axiom 3.4.21 ∏i { ⊢ T Type } { _ : T ⊢ U Type } ⊢ [∏](T,U) Type .

Axiom 3.4.22 ∏_eq { ⊢ T T' Type } { _ : T ⊢ U U' Type } [ T = T' ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒ [ [∏](T,U) = [∏](T',U') ].

Axiom 3.4.23 λ_hastype { ⊢ T Type } { _ : T ⊢ U Type } { x : T ⊢ o : U/x } ⊢ [λ](T,o) : [∏](T,U).

Axiom 3.4.24 λ_equality { ⊢ T T' Type } { _ : T ⊢ U U' Type } { x : T ⊢ o o' : U/x }

     			[ T = T' ] ⇒ ( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T',o') : [∏](T,U) ].

Axiom 3.4.24.1 λ_equality1 { ⊢ T T' Type } { x : T ⊢ U Type, o : U/x }

     			[ [λ](T,o) = [λ](T',o) : [∏](T,U) ].

Axiom 3.4.24.2 λ_equality2 { ⊢ T Type } { x : T ⊢ U U' Type, o o' : U/x } 

     			( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T,o') : [∏](T,U) ].

Axiom 3.4.25 ev { ⊢ T Type } { _ : T ⊢ U Type } { ⊢ f : [∏](T,U), o : T } ⊢ f o : U/o.

Axiom 3.4.26 ev_eq { ⊢ T Type, o o' : T } { _ : T ⊢ U U' Type } { ⊢ f f' : [∏](T,U) } 

	      [ f = f' : [∏](T,U) ] ⇒ [ o = o' : T ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒

	      [ [ev](f,o,U) = [ev](f',o',U') : U/o ].

# should make it possible to omit third branch of U here:

Axiom 3.4.27 beta_reduction { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U/x } [ [ev]([λ](T,o2),o1,U) = o2/o1 : U/o1 ].

Axiom 3.4.28 eta_reduction { ⊢ T Type } { _ : T ⊢ U Type } { ⊢ f : [∏](T,U) } [ [λ;x](T,[ev](f,x,U)) = f : [∏](T,U) ].

Axiom 3.4.29 j_type { ⊢ M1 M2 Ulevel } [ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ [j](M1,M2) : [U](M1) -> [U](M2) ].

Axiom 3.4.30 El_j_reduction { ⊢ M1 M2 Ulevel, o : [U](M1) } 

     		[ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ *[ev;_]([j](M1,M2),o,[U](M2)) = *o ].

Axiom 3.4.31 forall { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { x : *o1 ⊢ o2 : [U](M2) } ⊢ [∀](M1,M2,o1,o2) : [U]([max](M1,M2)).

Axiom 3.4.32 El_forall_reduction { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { _ : *o1 ⊢ o2 : [U](M2) }

          [ (*[∀](M1,M2,o1,o2)) = ([∏;x](*o1,[El](o2/x))) ].		# parser doesn't let us use *(o2/x); fix

Axiom 5.3.1 Pt_istype ⊢ [Pt]() Type. 

Check LF Pt_istype.

Axiom 5.3.2 tt_hastype ⊢ [tt]() : [Pt](). 

Axiom 5.3.3 Pt_eta { ⊢ o : [Pt]() } [ o = [tt]() : [Pt]() ].

Axiom 5.3.4 pt_hastype ⊢ [pt]() : [U](uu0).

Axiom 5.3.5 El_pt_reduction [ [El]([pt]()) = [Pt]() ].

Axiom 5.4.1 Pt_eliminator { ⊢ x : [Pt]() } { _ : [Pt]() ⊢ T Type } { ⊢ o : T/[tt]() } ⊢ [pt_r](o,T) : [Pi;x]([Pt](),T/x) .

Axiom 102 Empty ⊢ [Empty]() Type .

Axiom 100 teq_empty_eta { ⊢ a : [Empty](), T T' Type } [ T = T'].

Axiom 101 oeq_empty_eta { ⊢ a : [Empty](), T Type, o : T, o' : T } [ o = o' : T ].

Axiom 200 jMM_reduction { ⊢ M1 M2 Ulevel } [ M1 ~ M2 Ulevel ] ⇒ [ [j](M1,M2) = [λ;x]([U](M1),x) : [U](M1) -> [U](M2) ].

Axiom 201 jj_reduction { ⊢ M1 M2 M2' M3 Ulevel, o : [U](M1) }
		
		[ M2 ~ M2' Ulevel ] ⇒ [  [j](M2',M3) ([j](M1,M2) o) =  [j](M1,M3) o : [U](M1) -> [U](M3) ].


#   Local Variables:
#   compile-command: "make rules "
#   End:
