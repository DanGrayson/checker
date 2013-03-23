# -*- coding: utf-8 -*-

Include "rules/TS5.ts";;

Definition plus_one { ⊢ n : Nat } : Nat :=
	   n . ( @ev[S,n,Nat,_.Nat], n' . ev_hastype[Nat,_.Nat,S,n,SND,?,?,?,?] ) ;;

Definition LF plus_one' : oexp -> oexp := n |-> (@ev S n Nat (_ |-> Nat));;

Definition LF one' : oexp := (plus_one' O);;

Definition one_hastype' [ one' : Nat ] := ev_hastype[Nat,_.Nat,S,O,SND,?,?,?,?];;

Definition LF two' : oexp := (plus_one' one');;

Definition two_hastype' [ two' : Nat ] := ev_hastype[Nat,_.Nat,S,one',SND,?,?,?,?];;

Definition one : Nat := (plus_one[O,FST],plus_one[O,SND,O_hastype]);;

Definition two : Nat := (plus_one[one[FST],FST],plus_one[one[FST],SND,one[SND]]);;

Definition plus : Nat -> Nat -> Nat :=
 (
    lambda m:Nat, lambda n:Nat, @nat_r[ m, (lambda i:Nat, S), n, _.Nat ],
    λ_hastype[
       Nat,
       _ . Nat -> Nat,
       m . lambda n:Nat, @nat_r[ m, (lambda i:Nat, S), n, _.Nat ],
       SND,
       ?,
       _ . _ . ∏_istype[Nat, _ . Nat, SND, ?, ?],
       m . m' . λ_hastype[
       	  Nat,
	  _ . Nat,
	  n . @nat_r[ m, (lambda i:Nat, S), n, _.Nat ],
	  SND,
	  ?,
	  ?,
	  n . n' . nat_r_hastype[_.Nat,m,(lambda i:Nat, S),n,SND,?,?,
	  	λ_hastype[Nat, _ . Nat -> Nat, _ . S, SND, ?,_._.∏_istype[Nat, _.Nat, SND, ?,?],?],?]]]
    ) ;;

#   Local Variables:
#   compile-command: "make -C .. plus "
#   End:
