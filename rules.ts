# the derivation rules for TS0

Rule 7 tsimeq :

     Pi T:texp, Pi U:texp,
     [ T ~ U ] -> [ T = U ].

Rule 8 teqsymm :

     Pi T:texp, Pi U:texp,
     [ T = U ] -> [ U = T ].

Rule 9 teqtrans :

     Pi T:texp, Pi U:texp, Pi V:texp,
     [ T = U ] -> [ U = V ] -> [ T = V ].

Rule 10 osimeq :

     Pi x:oexp, Pi y:oexp, Pi T:texp,
     [ x ~ y : T ] -> [ x = y : T ].

Rule 11 oeqsymm :

     Pi x:oexp, Pi y:oexp, Pi T:texp,
     [ x = y : T ] -> [ y = x : T ].

Rule 12 oeqtrans :

     Pi x:oexp, Pi y:oexp, Pi z:oexp, Pi T:texp,
     [ x = y : T ] -> [ y = z : T ] -> [ x = z : T ].

Rule 13 cast :

     Pi o:oexp, Pi T:texp, Pi U:texp,
     [ o : T ] -> [ T = U ] -> [ o : U  ].

Rule 14 oeqcast :

     Pi x:oexp, Pi y:oexp, Pi T:texp, Pi U:texp,
     [ x = y : T ] -> [ T = U ] -> [ x = y : U ].

Rule 15 U_type :

     Pi M:uexp, 
     [ ([U] M) type ].

# Rule 16 u_univ :
# 
#      Pi M:uexp,
#      [ [u] M : [U] ([plus;1] M) ].

Rule 17 El_type :

     Pi M:uexp, Pi o:oexp,
     [ o : [U] M ] -> [ [El] o type ].

Rule 18 El_u_univ :

     Pi M:uexp,
     [ [El]([u] M) = [U] M ].

Rule 19 El_eq :

     Pi M:uexp, Pi x:oexp, Pi y:oexp, 
     [ x = y : [U] M ] -> [ [El] x = [El] y ].

Rule 20 El_eq_reflect :

     Pi M:uexp, Pi x:oexp, Pi y:oexp, 
     [ x : [U] M ] -> [ y : [U] M ] -> [ [El] x = [El] y ] -> [ x = y : [U] M ].

Rule 21 Pi_istype :

     Pi T:texp, Pi x:oexp, Pi U : oexp -> texp,
     [ x : T ] -> [ U x type ] -> [ [Pi] T U type ].

Rule 22 Pi_eq :

     Pi T:texp, Pi T':texp, 
     Pi U : oexp -> texp, Pi U' : oexp -> texp, 
     (Pi x:oexp, [ x : T ] -> [ U x = U' x])
     -> [ [Pi] T U = [Pi] T' U'  ].

Rule 23 lambda_hastype :

     Pi T:texp, Pi U:oexp->texp, Pi o:oexp->oexp,
     (Pi x:oexp, [ x : T ] -> [ o x : U x ])
     -> [ [lambda] T o : [Pi] T U ].

Rule 25 ev_hastype : 

     Pi T : texp, Pi U : oexp -> texp, Pi f : oexp, Pi o : oexp,
     [ f : [Pi] T U ] -> [ o : T ] -> [ [ev] f o U : U o].

Rule 26 ev_eq :

     Pi T : texp, Pi U : oexp -> texp, Pi f : oexp, Pi o : oexp,
     Pi T' : texp, Pi U' : oexp -> texp, Pi f' : oexp, Pi o' : oexp,
     (Pi x:oexp, [ x : T ] -> [ U x = U' x ]) -> 
     [ f = f' : [Pi] T U ] -> [ o = o' : T ] -> [ [ev] f o U = [ev] f' o' U' : U o].

Rule 27 beta_reduction :

     Pi T : texp, Pi U : oexp -> texp, Pi x : oexp, Pi y : oexp->oexp,
     [ x : T ] -> 
     (Pi x:oexp, [ y x : U x ]) ->
     [ [ev] ( [lambda] T y ) x U = y x : U x ].

Rule 28 eta_reduction :

     Pi T:texp, Pi U:oexp->texp, Pi f:oexp,
     [ f : [Pi] T U ] -> [ [lambda] T (lambda x, ([ev] f x (lambda y, (U y)))) = f : [Pi] T U ].

Rule 29 j_type :

     Pi M_1:uexp, Pi M_2:uexp, 
     uleq M_1 M_2 -> [ [j] M_1 M_2 : [Pi] ([U] M_1) (lambda _, ([U] M_2)) ].

Rule 30 El_j_reduction :

     Pi M_1:uexp, Pi M_2:uexp, Pi o:oexp,
     [ o : [U] M_1 ] -> uleq M_1 M_2 -> [ [El]( [ev] ([j] M_1 M_2) o (lambda _, ([U] M_2)) ) = [El] o ].

Rule 31 El_forall_reduction :

     Pi M_1:uexp, Pi M_2:uexp, Pi o_1:oexp, Pi o_2:oexp->oexp,
     ( Pi x:oexp, [ x : [El] o_1 ] -> [ o_2 x : [U] M_2 ] ) ->
     [ [El] ( [forall] M_1 M_2 o_1 o_2 ) : [U] ( [max] M_1 M_2 ) ].

Rule 32 type_El_forall :

     Pi M_1 : uexp, Pi M_2 : uexp, Pi o_1 : oexp, Pi o_2 : oexp -> oexp,
     [ o_1 : [U] M_1 ] ->
     (Pi x: oexp, [ x : [El] o_1 ] -> [ o_2 x : [U] M_2 ])
     ->
     [ [El] ([forall] M_1 M_2 o_1 o_2) = [Pi] ([El] o_1) (lambda x, ([El] (o_2 x))) ].
