# -*- coding: utf-8 -*-

Include "rules/TS6.ts".

# resizing rules
# @[rr0], @[rr1]

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

   := T ⟾ U ⟾ (_,_ ⟾ _ ⟾ ∏_istype[T, _ ⟾ U, CDR, _, _]).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

   := T ⟾ U ⟾ o ⟾ (_, _ ⟾ _ ⟾ λ_hastype[T, _ ⟾ U, o, CDR, _, _]).

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @[ev;_][f,o,T,U] : U

   := T ⟾ U ⟾ f ⟾ o ⟾ (_, _ ⟾ _ ⟾ ev_hastype[T, _ ⟾ U, f, o, CDR, _, _]).

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type

   := X ⟾ (_, 
        _ ⟾ Σ_istype[
		X, x ⟾ ∏ y:X, y=x, CDR, 
		_, x ⟾ _ ⟾ ∏_istype[
				X, y ⟾ @[Id][X,y,x], CDR,
				_, y ⟾ _ ⟾ Id_istype[X,y,x,CDR,_,_,_]]]).

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_][f,x,X,Y]=y  Type 

  := X ⟾ Y ⟾ f ⟾ y ⟾ (_, 
      _ ⟾ _ ⟾ _ ⟾ _ ⟾ 
      Σ_istype[
        X, x ⟾ @[ev;_][f,x,X,Y] = y, CDR, 
	_, x ⟾ _ ⟾ Id_istype[
			Y, ev1[X,Y,f,x,CAR], y, CDR, 
			_, ev1[X,Y,f,x,CDR,_,_,_,_],_]]).

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr[Hfiber[X,Y,f,y,CAR],CAR] Type 

   := X ⟾ Y ⟾ f ⟾ (_,
        _ ⟾ _ ⟾ _ ⟾ 
	  ∏_istype[
	     Y, y ⟾     Iscontr[ 
	     		    Hfiber[X,Y,f,y,CAR],CAR], CDR, 
 	     _, y ⟾ _ ⟾ Iscontr[
	     		    Hfiber[X,Y,f,y,CAR],CDR,
			    Hfiber[X,Y,f,y,CDR,_,_,_,_]]]).

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq[X,Y,f,CAR] Type 

   := X ⟾ Y ⟾ (_,
        _ ⟾ _ ⟾ Σ_istype[
	          pi1[X,Y,CAR],     f ⟾     Isweq[X,Y,f,CAR], CDR, 
 	  	  pi1[X,Y,CDR,_,_], f ⟾ _ ⟾ Isweq[X,Y,f,CDR,_,_,_]]).

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Iscontr[x=y,CAR] Type

   := X ⟾ (_,
        _ ⟾ 
	 ∏_istype[
 	   X, x ⟾ ∏ y:X, Iscontr [x=y,CAR], CDR,
	   _, x ⟾ _ ⟾ 
	        ∏_istype[
	  	   X, y ⟾ Iscontr[ 
		   		@[Id][X,x,y], CAR], CDR,
		   _, y ⟾ _ ⟾ Iscontr[
		  		@[Id][X,x,y], CDR,
 				Id_istype[X,x,y,CDR,_,_,_]]]]).

Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Isaprop[x=y,CAR] Type

   := X ⟾ (_,
        _ ⟾ ∏_istype[
	        X, x ⟾ ∏_istype[X, y ⟾ Isaprop[Id_istype[X,x,y,CAR],CAR],CAR], CDR,
		_, x ⟾ _ ⟾ 
		      ∏_istype[
		      	X, y ⟾  Isaprop[Id_istype[X,x,y,CAR],CAR],CDR,
			_, y ⟾ _ ⟾ 
				Isaprop[Id_istype[X,x,y,CAR],CDR,
					Id_istype[X,x,y,CDR,_,_,_]]]]).

Definition idfun { ⊢ X Type } ⊢ λ x:X,x : X⟶X

   := X ⟾ (_, _ ⟾ lambda1[X,X,x ⟾ x,CDR,_,_,_]).

# trying to prove the following theorem

# Theorem idisweq { ⊢ X Type } : Isweq[X,X,idfun[X,CAR],CAR] 
#    := _ .

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
