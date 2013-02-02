# -*- coding: utf-8 -*-

Include "rules/TS5.ts".

Definition plus_one { ⊢ n : Nat } : Nat := 
	   n ⟾ ( @[ev;_][S,n,Nat,Nat], n' ⟾ ev_hastype[Nat,_⟾Nat,S,n,CDR,_,_,_,_] ) .

Definition LF plus_one' : oexp -> oexp := n |-> (@[ev] S n Nat (_ |-> Nat)).

Definition LF one' : oexp := (plus_one' O).

Definition one'_hastype [ one' : Nat ] := ev_hastype[Nat,_⟾Nat,S,O,CDR,_,_,_,_].

Definition LF two' : oexp := (plus_one' one').

Definition two'_hastype [ two' : Nat ] := ev_hastype[Nat,_⟾Nat,S,one',CDR,_,_,_,_].

Definition one : Nat := (plus_one[O,CAR],plus_one[O,CDR,O_hastype]).

Definition two : Nat := (plus_one[one[CAR],CAR],plus_one[one[CAR],CDR,one[CDR]]).

Definition plus : Nat -> Nat -> Nat :=
 (
    lambda m:Nat, lambda n:Nat, @[nat_r;_][ m, (lambda i:Nat, S), n, Nat ],
    λ_hastype[
       Nat,
       _ ⟾ Nat -> Nat,
       m ⟾ lambda n:Nat, @[nat_r;_][ m, (lambda i:Nat, S), n, Nat ],
       CDR,
       _, 
       _ ⟾ _ ⟾ ∏_istype[Nat, _ ⟾ Nat, CDR, _, _], 
       m ⟾ m' ⟾ λ_hastype[
       	  Nat,
	  _ ⟾ Nat,
	  n ⟾ @[nat_r;_][ m, (lambda i:Nat, S), n, Nat ],
	  CDR,
	  _,
	  _,
	  n ⟾ n' ⟾ nat_r_hastype[_⟾Nat,m,(lambda i:Nat, S),n,CDR,_,_,
	  	λ_hastype[Nat, _ ⟾ Nat -> Nat, _ ⟾ S, CDR, _,_⟾_⟾∏_istype[Nat, _⟾Nat, CDR, _,_],_],_]]]
    ) .

#   Local Variables:
#   compile-command: "make -C .. plus "
#   End:
