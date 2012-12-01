# -*- coding: utf-8 -*-

# the derivation rules for TS0

Rule 7 tsimeq : ∏ T:texp, ∏ U:texp,

     [ T type ] ⟶ [ U type ] ⟶ [ T ~ U ] ⟶ [ T = U ].

Rule 8 teqsymm : ∏ T:texp, ∏ U:texp,

     [ T = U ] ⟶ [ U = T ].

Rule 9 teqtrans : ∏ T:texp, ∏ U:texp, ∏ V:texp,

     [ T = U ] ⟶ [ U = V ] ⟶ [ T = V ].

Rule 10 osimeq : ∏ x:oexp, ∏ y:oexp, ∏ T:texp,

     [ x ~ y : T ] ⟶ [ x = y : T ].

Rule 11 oeqsymm : ∏ x:oexp, ∏ y:oexp, ∏ T:texp,

     [ x = y : T ] ⟶ [ y = x : T ].

Rule 12 oeqtrans : ∏ x:oexp, ∏ y:oexp, ∏ z:oexp, ∏ T:texp,

     [ x = y : T ] ⟶ [ y = z : T ] ⟶ [ x = z : T ].

Rule 13 cast : ∏ o:oexp, ∏ T:texp, ∏ U:texp,

     [ o : T ] ⟶ [ T = U ] ⟶ [ o : U  ].

Rule 14 oeqcast : ∏ x:oexp, ∏ y:oexp, ∏ T:texp, ∏ U:texp,

     [ x = y : T ] ⟶ [ T = U ] ⟶ [ x = y : U ].

Rule 15 U_type : ∏ M:uexp, 

     [ ([U] M) type ].

Rule 16 u_univ : ∏ M:uexp,

     [ ([u] M) : ([U] ([next] M)) ].

Rule 17 El_type : ∏ M:uexp, ∏ o:oexp,

     [ o : ([U] M) ] ⟶ [ ([El] o) type ].

Rule 18 El_u_univ : ∏ M:uexp,

     [ ([El]([u] M)) = ([U] M) ].

Rule 19 El_eq : ∏ M:uexp, ∏ x:oexp, ∏ y:oexp, 

     [ x = y : ([U] M) ] ⟶ [ ([El] x) = ([El] y) ].

Rule 20 El_eq_reflect : ∏ M:uexp, ∏ x:oexp, ∏ y:oexp, 

     [ x : ([U] M) ] ⟶ [ y : ([U] M) ] ⟶ 

     [ ([El] x) = ([El] y) ] ⟶ [ x = y : ([U] M) ].

Rule 21 ∏_istype : ∏ T:texp, ∏ U : oexp ⟶ texp,

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) type ]) ⟶ [ ([∏] T U) type ].

Rule 22 ∏_eq : ∏ T:texp, ∏ T':texp, ∏ U : oexp ⟶ texp, ∏ U' : oexp ⟶ texp, 

     [ T = T' ] ⟶

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) = (U' x)])

     ⟶ [ ([∏] T U) = ([∏] T' U')  ].

Rule 23 λ_hastype : ∏ T:texp, ∏ U:oexp ⟶ texp, ∏ o:oexp ⟶ oexp,

     [ T type ] ⟶

     (∏ x:oexp, [ x : T ] ⟶ [ (o x) : (U x) ]) ⟶

     [ ([λ] T o) : ([∏] T U) ].

Rule 25 ev_hastype : ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ f : oexp, ∏ o : oexp,

     [ f : ([∏] T U) ] ⟶ 
     [ o : T ] ⟶ 
     [ ([ev] f o U) : (U o)].

Rule 26 ev_eq : ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ f : oexp, ∏ o : oexp,
     ∏ T' : texp, ∏ U' : oexp ⟶ texp, ∏ f' : oexp, ∏ o' : oexp,

     (∏ x:oexp, [ x : T ] ⟶ [ (U x) = (U' x) ]) ⟶ 
     [ f = f' : ([∏] T U) ] ⟶ 
     [ o = o' : T ] ⟶ 
     [ ([ev] f o U) = ([ev] f' o' U') : (U o)].

Rule 27 beta_reduction : ∏ T : texp, ∏ U : oexp ⟶ texp, ∏ x : oexp, ∏ y : oexp ⟶ oexp,

     [ x : T ] ⟶ 
     (∏ x:oexp, [ (y x) : (U x) ]) ⟶
     [ ([ev] ( [λ] T y ) x U) = (y x) : (U x) ].

Rule 28 eta_reduction : ∏ T:texp, ∏ U:oexp ⟶ texp, ∏ f:oexp,

     [ f : ([∏] T U) ] ⟶ 
     [ ( [λ] T (x ⟼ ([ev] f x (y ⟼ (U y))))) = f : ([∏] T U) ].

Rule 29 j_type : ∏ M_1:uexp, ∏ M_2:uexp, 

     uequal ([max] M_1 M_2) M_2 ⟶ [ ([j] M_1 M_2) : ([∏] ([U] M_1) (_ ⟼ ([U] M_2))) ].

Rule 30 El_j_reduction : ∏ M_1:uexp, ∏ M_2:uexp, ∏ o:oexp,

     [ o : ([U] M_1) ] ⟶ uequal ([max] M_1 M_2) M_2 ⟶ [ ([El]( [ev] ([j] M_1 M_2) o (_ ⟼ ([U] M_2)) )) = ([El] o) ].

Rule 31 El_forall_reduction : ∏ M_1:uexp, ∏ M_2:uexp, ∏ o_1:oexp, ∏ o_2:oexp ⟶ oexp,

     ( ∏ x:oexp, [ x : ([El] o_1) ] ⟶ [ (o_2 x) : ([U] M_2) ] ) ⟶
     [ ( [∀] M_1 M_2 o_1 o_2 ) : ([U] ( [max] M_1 M_2 )) ].

Rule 32 type_El_forall : ∏ M_1 : uexp, ∏ M_2 : uexp, ∏ o_1 : oexp, ∏ o_2 : oexp ⟶ oexp,

     [ o_1 : ([U] M_1) ] ⟶
     (∏ x: oexp, [ x : ([El] o_1) ] ⟶ [ (o_2 x) : ([U] M_2) ]) ⟶
     [ ([El] ([∀] M_1 M_2 o_1 o_2)) = ([∏] ([El] o_1) (x ⟼ ([El] (o_2 x)))) ].

Rule 100 teq_empty_eta : ∏ T:texp, ∏ T':texp, ∏ a:oexp,

     [ a : ([Empty]) ] ⟶ [ T type ] ⟶ [ T' type ] ⟶ [ T = T'].

Rule 101 oeq_empty_eta : ∏ T:texp, ∏ x:oexp, ∏ y:oexp, ∏ a:oexp,

     [ a : ([Empty]) ] ⟶ [ x : T ] ⟶ [ y : T ] ⟶ [ x = y : T ].
