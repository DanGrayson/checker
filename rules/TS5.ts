# -*- coding: utf-8 -*-

Include "rules/TS4.ts".

Axiom 15.5.1 nat_hastype ⊢ nat : UU[uu0].

Lemma Nat_istype [ Nat Type ] := El_istype[uu0,nat,CDR,nat_hastype[CDR]].

Axiom 15.5.2 O_hastype ⊢ O : Nat.

Axiom 15.5.3 S_hastype [ S : Nat -> Nat ].

Axiom 15.5.4 nat_r_hastype { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @[ev;_][S,x,Nat,Nat] ] } 

      { ⊢ n : Nat } ⊢ @[nat_r][o1,o2,n,T] : T[n].

Axiom 15.3.1.2 nat_O_reduction { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @[ev;_][S,x,Nat,Nat] ] } 

      [ @[nat_r][o1,o2,O,T] ≡ o1 : T[O] ].

Lemma nat_S_reduction_sanity1 { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @[ev;_][S,x,Nat,Nat] ] } 
      { ⊢ n : Nat } 
      [   @[nat_r][o1,o2,@[ev;_][S,n,Nat,Nat],T] 
	  :
	  T[@[ev;_][S,n,Nat,Nat]] ] := 

      T ⟾ T' ⟾ o1 ⟾ o1' ⟾ o2 ⟾ o2' ⟾ n ⟾ n' ⟾ 
      nat_r_hastype[
      	T, o1, o2, @[ev;_][S,n,Nat,Nat], CDR,
	T', o1', o2', ev_hastype[Nat,_⟾Nat,S,n,CDR,Nat_istype,_⟾_⟾Nat_istype,S_hastype,_]
	].

Axiom 15.3.1.3 nat_S_reduction { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @[ev;_][S,x,Nat,Nat] ] } 

      { ⊢ n : Nat } 

      [   @[nat_r][o1,o2,@[ev;_][S,n,Nat,Nat],T] 
          ≡ 
  	  @[ev;_][@[ev;x][o2,n,Nat,T[x]->T[@[ev;_][S,x,Nat,Nat]]],@[nat_r][o1,o2,n,T],Nat,T[@[ev;_][S,n,Nat,Nat]]]
	  :
	  T[@[ev;_][S,n,Nat,Nat]] ].

Axiom nat_eta { x : Nat ⊢ T Type }

      { ⊢ o1 o1' : T[O] } 

      [ o1 ≡ o1' : T[O] ]

      { ⊢ o2 o2' : ∏ x:Nat, T[x] -> T[ @[ev;_][S,x,Nat,Nat] ] }

      ({ ⊢ n : Nat } { ⊢ t : T[n] } [ 

      		@[ev;_][@[ev;x][o2,n,Nat,T[x]->T[@[ev;_][S,x,Nat,Nat]]],t,T[n],T[@[ev;_][S,n,Nat,Nat]]]

		≡

      		@[ev;_][@[ev;x][o2',n,Nat,T[x]->T[@[ev;_][S,x,Nat,Nat]]],t,T[n],T[@[ev;_][S,n,Nat,Nat]]]

		: 

		T[@[ev;_][S,n,Nat,Nat]]

	   ]) ⇒

      { ⊢ n : Nat } [ @[nat_r][o1,o2,n,T] ≡ @[nat_r][o1',o2',n,T] : T[n] ].

#   Local Variables:
#   compile-command: "make -C .. rules5 "
#   End:
