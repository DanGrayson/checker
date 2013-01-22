# -*- coding: utf-8 -*-

Mode Relative.

Include "rules/TS6.ts".

# resizing rules
# @[rr0], @[rr1]

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

   := T ⟾ U ⟾ (_,T' ⟾ U' ⟾ ∏_istype[T, _ ⟾ U, CDR, T', _ ⟾ _ ⟾ U']).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

   := T ⟾ U ⟾ o ⟾ (_, T' ⟾ U' ⟾ λ_hastype[T, _ ⟾ U, o, CDR, _, _]).

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @[ev;_][f,o,U] : U

   := T ⟾ U ⟾ f ⟾ o ⟾ (_, T' ⟾ U' ⟾ ev_hastype[T, _ ⟾ U, f, o, CDR, _, _]).

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type

   := X ⟾ (_, 
	  X' ⟾ Σ_istype[X, x ⟾ ∏ y:X, y=x, CDR, _, x ⟾ x' ⟾ ∏_istype[X, y ⟾ @[Id][X,y,x], CDR, _, y ⟾ y' ⟾ Id_istype[X,y,x,CDR,_,_,_]]]).

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_][f,x,Y]=y  Type 

  := X ⟾ Y ⟾ f ⟾ y ⟾ (_, 
     X' ⟾ Y' ⟾ f' ⟾ y' ⟾ Σ_istype[X, x ⟾ @[ev;_][f,x,Y] = y, CDR, _, 
      		   x ⟾ x' ⟾ Id_istype[Y, ev1[X,Y,f,x,CAR], y, CDR, _, ev1[X,Y,f,x,CDR,_,_,_,_],_]]).

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr[Hfiber[X,Y,f,y,CAR],CAR] Type 

   := X ⟾ Y ⟾ f ⟾ (_,
        X' ⟾ Y' ⟾ f' ⟾ ∏_istype[Y, 
          y ⟾ Iscontr[ Hfiber[X,Y,f,y,CAR],CAR], CDR, _,
          y ⟾ y' ⟾ Iscontr[Hfiber[X,Y,f,y,CAR],CDR,Hfiber[X,Y,f,y,CDR,_,_,_,_]]]).

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq[X,Y,f,CAR] Type 

   := X ⟾ Y ⟾ (_,
        X' ⟾ Y' ⟾ Σ_istype[
	  pi1[X,Y,CAR], 
 	  f ⟾ Isweq[X,Y,f,CAR], 
	  CDR, 
 	  pi1[X,Y,CDR,_,_], 
 	  f ⟾ f' ⟾ Isweq[X,Y,f,CDR,_,_,_]]).

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Iscontr[x=y,CAR] Type

   := X ⟾ (_,
        X' ⟾ ∏_istype[
 	  X, 
	    x ⟾ ∏ y:X, Iscontr [ x=y,CAR ],
	  CDR,
	  _,
 	    x ⟾ x' ⟾ ∏_istype[
	  	X, 
		 y ⟾ Iscontr[ @[Id][X,x,y],CAR],
		CDR,
		_,
 	     	  y ⟾ y' ⟾ Iscontr[
		  		Id_istype[X,x,y,CAR],
				CDR,
 				Id_istype[X,x,y,CDR,_,_,_]]]]).


Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Isaprop[x=y,CAR] Type

   := X ⟾ (_,
        X' ⟾ ∏_istype[X, x ⟾ ∏_istype[X, y ⟾ Isaprop[Id_istype[X,x,y,CAR],CAR],CAR], CDR,_,
 	   x ⟾ x' ⟾ ∏_istype[X, 
 	     y ⟾ Isaprop[Id_istype[X,x,y,CAR],CAR],CDR,_,
 	       y ⟾ y' ⟾ Isaprop[Id_istype[X,x,y,CAR],CDR,Id_istype[X,x,y,CDR,_,_,_]]]]).

Definition idfun { ⊢ X Type } ⊢ λ x:X,x : X⟶X

   := X ⟾ (_, X' ⟾ lambda1[X,X,x ⟾ x,CDR,_,_,x ⟾ x' ⟾ x']).

End.

Theorem idisweq { ⊢ X Type } : Isweq₁[X,X,idfun₁[X]] 
   := ??? .

#   Local Variables:
#   compile-command: "make -C .. rules7r "
#   End:
