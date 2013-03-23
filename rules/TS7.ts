# -*- coding: utf-8 -*-

Include "rules/TS6.ts";;

# resizing rules
# @rr0, @rr1

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

   := T.U.(?,..∏_istype[T,.U,SND,?,?]);;

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

   := T.U.o.(?,..λ_hastype[T,.U,o,SND,?,?]);;

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @ev[f,o,T,.U] : U

   := T.U.f.o.(?,..ev_hastype[T,.U,f,o,SND,?,?]);;

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, Id[X,y,x]  Type

   := X.(?,
        .Σ_istype[
		X, x.∏ y:X, Id[X,y,x], SND,
		?, x..∏_istype[
				X, y.Id[X,y,x], SND,
				?, y..Id_istype[X,y,x,SND,?,?,?]]]);;

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, Id[Y,@ev[f,x,X,.Y],y]  Type

  := X.Y.f.y.(?,
      ....Σ_istype[
        X, x.Id[Y, @ev[f,x,X,.Y], y], SND,
	?, x..Id_istype[
			Y, ev1[X,Y,f,x,FST], y, SND,
			?, ev1[X,Y,f,x,SND,?,?,?,?],?]]);;

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr[Hfiber[X,Y,f,y,FST],FST] Type

   := X.Y.f.(?,
        ...∏_istype[
	     Y, y.Iscontr[
	     		    Hfiber[X,Y,f,y,FST],FST], SND,
 	     ?, y..Iscontr[
	     		    Hfiber[X,Y,f,y,FST],SND,
			    Hfiber[X,Y,f,y,SND,?,?,?,?]]]);;

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq[X,Y,f,FST] Type

   := X.Y.(?,
        ..Σ_istype[
	          pi1[X,Y,FST],     f.Isweq[X,Y,f,FST], SND,
 	  	  pi1[X,Y,SND,?,?], f.f'.Isweq[X,Y,f,SND,?,?,f']]);;

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Iscontr[Id[X,x,y],FST] Type

   := X.(?,
        .∏_istype[
 	   X, x.∏ y:X, Iscontr [Id[X,x,y],FST], SND,
	   ?, x..∏_istype[
	  	   X, y.Iscontr[
		   		Id[X,x,y], FST], SND,
		   ?, y..Iscontr[
		  		Id[X,x,y], SND,
 				Id_istype[X,x,y,SND,?,?,?]]]]);;

Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Isaprop[Id[X,x,y],FST] Type

   := X.(?,
        .∏_istype[
	        X, x.∏_istype[X, y.Isaprop[Id_istype[X,x,y,FST],FST],FST], SND,
		?, x..∏_istype[
		      	X, y.Isaprop[Id_istype[X,x,y,FST],FST],SND,
			?, y..Isaprop[Id_istype[X,x,y,FST],SND,
					Id_istype[X,x,y,SND,?,?,?]]]]);;

Definition idfun { ⊢ X Type } ⊢ λ x:X,x : X⟶X

   := X.(?, .lambda1[X,X,x.x,SND,?,?,?]);;

# trying to prove the following theorem

# Theorem idisweq { ⊢ X Type } : Isweq[X,X,idfun[X,FST],FST]
#    := _ ;;

#   Local Variables:
#   compile-command: "make -C .. TS7 "
#   End:
