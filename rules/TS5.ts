# -*- coding: utf-8 -*-

Include "rules/TS4.ts".

Definition LF nat : oexp := @nat.

Axiom 15.5.1 nat_hastype [ nat : UU[uu0] ].

Definition LF Nat : texp := (El nat).

Check LF Nat.

Lemma Nat_istype [ Nat Type ] := El_istype[uu0,nat,SND,nat_hastype].

Definition Nat' Type := (*nat, El_istype[uu0,nat,SND,nat_hastype]).

Axiom 15.5.2 O_hastype [ O : Nat ].

Axiom 15.5.3 S_hastype [ S : Nat -> Nat ].

Axiom 15.5.4 nat_r_hastype { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }

      { ⊢ n : Nat } ⊢ @nat_r[o1,o2,n,T] : T[n].

Axiom 15.3.1.2 nat_O_reduction { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }

      [ @nat_r[o1,o2,O,T] ≡ o1 : T[O] ].

Lemma nat_S_reduction_sanity1 { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }
      { ⊢ n : Nat }
      [   @nat_r[o1,o2,@ev[S,n,Nat,_.Nat],T]
	  :
	  T[@ev[S,n,Nat,_.Nat]] ] :=

      T.T'.o1.o1'.o2.o2'.n.n'.(
      nat_r_hastype[
      	T, o1, o2, @ev[S,n,Nat,_.Nat], SND,
	T',_, _, ev_hastype[Nat,_.Nat,S,n,SND,Nat_istype,_._.Nat_istype,S_hastype,_]
	]).

Lemma nat_S_reduction_sanity2 { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }
      { ⊢ n : Nat }
      [   @ev[@ev[o2,n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],@nat_r[o1,o2,n,T],T[n],_.T[@ev[S,n,Nat,_.Nat]]]
	  :
	  T[@ev[S,n,Nat,_.Nat]] ] :=

      T.T'.o1.o1'.o2.o2'.n.n' ⟾
      ev_hastype[
          T[n],
	  _.T[@ev[S,n,Nat,_.Nat]],
	  @ev[o2,n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],
	  @nat_r[o1,o2,n,T],
	  SND,
          T'[n,_],
	  _._.T'[@ev[S,n,Nat,_.Nat],ev_hastype[Nat,_.Nat,S,n,SND,_,_,_,_]],
	  ev_hastype[
	  	Nat, x.T[x]->T[@ev[S,x,Nat,_.Nat]], o2, n, SND,
		_, x.x'.∏_istype[T[x],_.T[@ev[S,x,Nat,_.Nat]],SND,T'[x,_],_._.T'[@ev[S,x,Nat,_.Nat],ev_hastype[Nat,_.Nat,S,x,SND,_,_,_,_]]],
		_, _],
	  nat_r_hastype[T,o1,o2,n,SND,T',_,_,_]].

Axiom 15.3.1.3 nat_S_reduction { x : Nat ⊢ T Type } { ⊢ o1 : T[O] } { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }

      { ⊢ n : Nat }

      [   @nat_r[o1,o2,@ev[S,n,Nat,_.Nat],T]
          ≡
	  @ev[@ev[o2,n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],@nat_r[o1,o2,n,T],T[n],_.T[@ev[S,n,Nat,_.Nat]]]
	  :
	  T[@ev[S,n,Nat,_.Nat]] ].

Lemma nat_equality_sanity { x : Nat ⊢ T Type }
      { ⊢ o1 : T[O] }
      { ⊢ o2 : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }
      { ⊢ n : Nat } { ⊢ t : T[n] } [
      		@ev[@ev[o2,n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],t,T[n],_.T[@ev[S,n,Nat,_.Nat]]]
		:
		T[@ev[S,n,Nat,_.Nat]]
	   ] :=
   T.T'.o1.o1'.o2.o2'.n.n'.t.t'.(
   ev_hastype[
      T[n], _.T[@ev[S,n,Nat,_.Nat]], @ev[o2,n,Nat,x.T[x] -> T[@ev[S,x,Nat,_.Nat]]], t, SND,
      T'[n,n'],
      _._.T'[@ev[S,n,Nat,_.Nat],ev_hastype[Nat,_.Nat,S,n,SND,_,_,_,_]],
      ev_hastype[
      	  Nat, x.T[x] -> T[@ev[S,x,Nat,_.Nat]], o2, n, SND,
	  _, x.x'.∏_istype[T[x],_.T[@ev[S,x,Nat,_.Nat]],SND,T'[x,_],_._.T'[@ev[S,x,Nat,_.Nat],ev_hastype[Nat,_.Nat,S,x,SND,_,_,_,_]]], _, _],
      _]).

Axiom nat_equality
      { x : Nat ⊢ T Type }
      { ⊢ o1 o1' : T[O] } [ o1 ≡ o1' : T[O] ]
      { ⊢ o2 o2' : ∏ x:Nat, T[x] -> T[ @ev[S,x,Nat,_.Nat] ] }
      ({ ⊢ n : Nat } { ⊢ t : T[n] } [
      		@ev[@ev[o2,n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],t,T[n],_.T[@ev[S,n,Nat,_.Nat]]]
		≡
      		@ev[@ev[o2',n,Nat,x.T[x]->T[@ev[S,x,Nat,_.Nat]]],t,T[n],_.T[@ev[S,n,Nat,_.Nat]]]
		:
		T[@ev[S,n,Nat,_.Nat]] ]) ⇒
      { ⊢ n : Nat }
      [ @nat_r[o1,o2,n,T] ≡ @nat_r[o1',o2',n,T] : T[n] ].

Axiom nat_eta
      { n : Nat ⊢ T Type, f g : T[n] }
      [ f[O] ≡ g[O] : T[O] ] ⇒
      ({ ⊢ n : Nat } [ f[n] ≡ g[n] : T[n] ] ⇒ [ f[@ev[S,n,Nat,_.Nat]] ≡ g[@ev[S,n,Nat,_.Nat]] : T[@ev[S,n,Nat,_.Nat]] ]) ⇒
      { ⊢ n : Nat } [ f[n] ≡ g[n] : T[n] ].

#   Local Variables:
#   compile-command: "make -C .. rules5 "
#   End:
