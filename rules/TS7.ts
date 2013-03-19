# -*- coding: utf-8 -*-

Include "rules/TS6.ts";;

# resizing rules
# @rr0, @rr1

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

   := T.U.(_,..∏_istype[T,.U,SND,_,_]);;

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

   := T.U.o.(_,..λ_hastype[T,.U,o,SND,_,_]);;

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @ev[f,o,T,.U] : U

   := T.U.f.o.(_,..ev_hastype[T,.U,f,o,SND,_,_]);;

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, Id[X,y,x]  Type

   := X.(_,
        .Σ_istype[
		X, x.∏ y:X, Id[X,y,x], SND,
		_, x..∏_istype[
				X, y.Id[X,y,x], SND,
				_, y..Id_istype[X,y,x,SND,_,_,_]]]);;

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, Id[Y,@ev[f,x,X,.Y],y]  Type

  := X.Y.f.y.(_,
      ....Σ_istype[
        X, x.Id[Y, @ev[f,x,X,.Y], y], SND,
	_, x..Id_istype[
			Y, ev1[X,Y,f,x,FST], y, SND,
			_, ev1[X,Y,f,x,SND,_,_,_,_],_]]);;

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr[Hfiber[X,Y,f,y,FST],FST] Type

   := X.Y.f.(_,
        ...∏_istype[
	     Y, y.Iscontr[
	     		    Hfiber[X,Y,f,y,FST],FST], SND,
 	     _, y..Iscontr[
	     		    Hfiber[X,Y,f,y,FST],SND,
			    Hfiber[X,Y,f,y,SND,_,_,_,_]]]);;

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq[X,Y,f,FST] Type

   := X.Y.(_,
        ..Σ_istype[
	          pi1[X,Y,FST],     f.Isweq[X,Y,f,FST], SND,
 	  	  pi1[X,Y,SND,_,_], f.f'.Isweq[X,Y,f,SND,_,_,f']]);;

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Iscontr[Id[X,x,y],FST] Type

   := X.(_,
        .∏_istype[
 	   X, x.∏ y:X, Iscontr [Id[X,x,y],FST], SND,
	   _, x..∏_istype[
	  	   X, y.Iscontr[
		   		Id[X,x,y], FST], SND,
		   _, y..Iscontr[
		  		Id[X,x,y], SND,
 				Id_istype[X,x,y,SND,_,_,_]]]]);;

Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Isaprop[Id[X,x,y],FST] Type

   := X.(_,
        .∏_istype[
	        X, x.∏_istype[X, y.Isaprop[Id_istype[X,x,y,FST],FST],FST], SND,
		_, x..∏_istype[
		      	X, y.Isaprop[Id_istype[X,x,y,FST],FST],SND,
			_, y..Isaprop[Id_istype[X,x,y,FST],SND,
					Id_istype[X,x,y,SND,_,_,_]]]]);;

Definition idfun { ⊢ X Type } ⊢ λ x:X,x : X⟶X

   := X.(_, .lambda1[X,X,x.x,SND,_,_,_]);;

# trying to prove the following theorem

# Theorem idisweq { ⊢ X Type } : Isweq[X,X,idfun[X,FST],FST]
#    := _ ;;

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
