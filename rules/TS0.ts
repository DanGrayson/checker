# -*- coding: utf-8 -*-

Variable uu0 Ulevel.

Axiom 3.4.7 tsimeq { ⊢ T U Type } [ T ~ U Type ] ⇒ [ T = U ].

Axiom 3.4.8 teqsymm { ⊢ T U Type } [ T = U ] ⇒ [ U = T ].

Axiom 3.4.9 teqtrans { ⊢ T U V Type } [ T = U ] ⇒ [ U = V ] ⇒ [ T = V ].

Axiom 3.4.10 osimeq { ⊢ T Type, x y : T } [ x ~ y : T ] ⇒ [ x = y : T ].

Axiom 3.4.11 oeqsymm { ⊢ T Type, x : T, y : T } [ x = y : T ] ⇒ [ y = x : T ].

Axiom 3.4.12 oeqtrans { ⊢ T Type, x : T, y : T, z : T } [ x = y : T ] ⇒ [ y = z : T ] ⇒ [ x = z : T ].

Axiom 3.4.13 cast { ⊢ T U Type } [ T = U ] ⇒ { ⊢ o : T } ⊢ o : U.

Axiom 3.4.14 oeqcast { ⊢ T U Type, x : T, y : T } [ x = y : T ] ⇒ [ T = U ] ⇒ [ x = y : U ].

Axiom 3.4.15 UU { ⊢ M Ulevel } ⊢ [U](M) Type.

Axiom 3.4.16 uu { ⊢ M Ulevel } ⊢ [u](M) : [U]([next](M)).

Axiom 3.4.17 El { ⊢ M Ulevel, o : [U](M) } ⊢ *o Type.

Axiom 3.4.18 El_u_reduction { ⊢ M Ulevel } [ *[u](M) = [U](M) ].

Axiom 3.4.19 El_eq { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ x = y : [U](M) ] ⇒ [ *x = *y ].

Axiom 3.4.20 El_eq_reflect { ⊢ M Ulevel, x : [U](M), y : [U](M) } [ *x = *y ] ⇒ [ x = y : [U](M) ].

Axiom 3.4.21 pi { ⊢ T Type } { t : T ⊢ U Type } ⊢ [∏;t](T,U/t) Type .

Axiom 3.4.22 ∏_eq { ⊢ T T' Type } { t : T ⊢ U U' Type } [ T = T' ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒ [ [∏;t](T,U/t) = [∏;t](T',U'/t) ].

Axiom 3.4.23 λh { ⊢ T Type } { x : T ⊢ U Type, o : U/x } ⊢ [λ](T,o) : [∏;t](T,U/t).

Axiom 3.4.24 λ_equality { ⊢ T T' Type } { x : T ⊢ U U' Type, o o' : U/x }

     			[ T = T' ] ⇒ ( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T',o') : [∏](T,U) ].

Axiom 3.4.24.1 λ_equality1 { ⊢ T T' Type } { x : T ⊢ U Type, o : U/x }

     			[ [λ](T,o) = [λ](T',o) : [∏;t](T,U/t) ].

Axiom 3.4.24.2 λ_equality2 { ⊢ T Type } { x : T ⊢ U U' Type, o o' : U/x } 

     			( { ⊢ x : T } [ o/x = o'/x : U/x ] ) ⇒ 

			[ [λ](T,o) = [λ](T,o'): [∏;t](T,U/t) ].

Axiom 3.4.25 ev { ⊢ T Type } { t : T ⊢ U Type } { ⊢ f : [∏](T,U), o : T } ⊢ [ev;t](f,o,U/t) : U/o.

Axiom 3.4.26 ev_eq { ⊢ T Type, o o' : T } { t : T ⊢ U U' Type } { ⊢ f f' : [∏;t](T,U/t) } 

	      [ f = f' : [∏;t](T,U/t) ] ⇒ [ o = o' : T ] ⇒ ( { ⊢ x : T } [ U/x = U'/x ] ) ⇒

	      [ [ev](f,o,U) = [ev](f',o',U') : U/o ].

Axiom 3.4.27 beta_reduction { ⊢ T Type, o1 : T } { x : T ⊢ U Type, o2 : U/x } [ [ev;t]([λ;t](T,o2/t),o1,U/t) = o2/o1 : U/o1 ].

Axiom 3.4.28 eta_reduction { ⊢ T Type } { t : T ⊢ U Type } { ⊢ f : [∏;t](T,U/t) } [ [λ;x](T,[ev;t](f,x,U/t)) = f : [∏;t](T,U/t) ].

Axiom 3.4.29 jj { ⊢ M1 M2 Ulevel } [ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ [j](M1,M2) : [U](M1) -> [U](M2) ].

Axiom 3.4.30 El_j_reduction { ⊢ M1 M2 Ulevel, o : [U](M1) } 

     		[ [max](M1,M2) ~ M2 Ulevel ] ⇒ [ *[ev;_]([j](M1,M2),o,[U](M2)) = *o ].

Axiom 3.4.31 forall { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { x : *o1 ⊢ o2 : [U](M2) } ⊢ [∀;t](M1,M2,o1,o2/t) : [U]([max](M1,M2)).

Axiom 3.4.32 El_forall_reduction { ⊢ M1 M2 Ulevel, o1 : [U](M1) } { x : *o1 ⊢ o2 : [U](M2) }

          [ (*[∀;x](M1,M2,o1,o2/x)) = ([∏;x](*o1,[El](o2/x))) ].		# parser doesn't let us use *(o2/x); fix

#   Local Variables:
#   compile-command: "make -C .. rules0 "
#   End:
