# -*- coding: utf-8 -*-

Mode Pairs.

Include "rules/TS6.ts".

# resizing rules
# @[rr0], @[rr1]

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

	   := (_, T ⟾ U ⟾ ∏_istype₂[T,(_⟾U₁,_⟾U)]).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

	   := (_, T ⟾ U ⟾ λ_hastype₂[T,(_⟾U₁,_⟾U)]).

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @[ev;_][f,o,U] : U

	   := (_, T ⟾ U ⟾ ev_hastype₂[T,(_⟾U₁,_⟾U)]).

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type

	   := (_, X ⟾ Σ_istype₂[X, (x ⟾ ∏ y:X₁, y=x, 
   			                x' ⟾ ∏_istype₂[X,(y ⟾ y=x'₁, 
			 	                    y' ⟾ Id_istype₂[X,y',x'])])]).

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_][f,x,Y]=y  Type 

  := (_, X ⟾ Y ⟾ f ⟾ y ⟾ 
     Σ_istype₂[X, (x ⟾ @[ev;_][f₁,x,Y₁] = y₁,
      		   x ⟾ Id_istype₂[Y, ev1₂[X,Y,f,x], y])]).

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr₁[Hfiber₁[X,Y,f,y]] Type 

   := (_,X ⟾ Y ⟾ f ⟾ ∏_istype₂[Y, (y ⟾ Iscontr₁[ Hfiber₁[X₁,Y₁,f₁,y]], 
   				    y' ⟾ Iscontr₂[ Hfiber₂[X,Y,f,y']])]).

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq₁[X,Y,f] Type 

   := (_,X ⟾ Y ⟾ Σ_istype₂[pi1₂[X,Y], 
   		(f ⟾ Isweq₁[X₁,Y₁,f], 
   		 f' ⟾ Isweq₂[X,Y,f'])]).

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Iscontr₁[x=y] Type

   := (_,X ⟾ ∏_istype₂[X, (x ⟾ ∏ y:X₁, Iscontr₁ [ x=y ],
   		            x' ⟾ ∏_istype₂[X, (y ⟾ Iscontr₁[ x'₁=y],
		       		                y' ⟾ Iscontr₂[Id_istype₂[X,x',y']])])]).

Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ y:X, Isaprop₁[x=y] Type

   := (_,X ⟾ ∏_istype₂[X, (x ⟾ ∏_istype₁[X₁, y ⟾ Isaprop₁[Id_istype₁[X₁,x,y]]], 
   		            x' ⟾ ∏_istype₂[X, 
			    		     (y ⟾ Isaprop₁[Id_istype₁[X₁,x'₁,y]],
		       		              y' ⟾ Isaprop₂[Id_istype₂[X,x',y']])])]).

Definition idfun { ⊢ X Type } ⊢ λ x:X,x : X⟶X

   := (_,X ⟾ lambda1₂[X,X,(x ⟾ x,x ⟾ x)]).

End.

Theorem idisweq { ⊢ X Type } : Isweq₁[X,X,idfun₁[X]] 
   := ??? .

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
