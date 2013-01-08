# -*- coding: utf-8 -*-

Mode Pairs.

Include "rules/TS6.ts".

# resizing rules
# @[rr0], @[rr1]

Definition pi1 { ⊢ T U Type } ⊢ T⟶U Type

	   := (_, T ⟾ U ⟾ pi₂[T,(_⟾U₁,_⟾U)]).

Definition lambda1 { ⊢ T U Type } { t : T ⊢ o : U } ⊢ λ t:T, o[t] : T⟶U

	   := (_, T ⟾ U ⟾ λh₂[T,(_⟾U₁,_⟾U)]).

Definition ev1 { ⊢ T U Type, f:T⟶U, o:T } ⊢ @[ev;_](f,o,U) : U

	   := (_, T ⟾ U ⟾ ev_hastype₂[T,(_⟾U₁,_⟾U)]).

Check LF ev_hastype.

Definition Iscontr { ⊢ X Type } ⊢ Σ x:X, ∏ y:X, y=x  Type

	   := (_, X ⟾ Σ_istype₂[X, (x ⟾ ∏ y:X₁, y=x, 
   			                x' ⟾ pi₂[X,(y ⟾ y=x'₁, 
			 	                    y' ⟾ Id_istype₂[X,y',x'])])]).

Definition Hfiber { ⊢ X Y Type, f:X⟶Y, y:Y } ⊢ Σ x:X, @[ev;_](f,x,Y)=y  Type 

  := (_, X ⟾ Y ⟾ f ⟾ y ⟾ 
     Σ_istype₂[X, (x ⟾ @[ev](f₁, x, _ ⟾ Y₁)=y₁,
      		   x ⟾ Id_istype₂[Y, ev1₂[X,Y,f,x], y])]).

Definition Isweq { ⊢ X Y Type, f:X⟶Y } ⊢ ∏ y:Y, Iscontr₁[Hfiber₁[X,Y,f,y]] Type 

   ::= (_,X ⟼ Y ⟼ f ⟼ (pi₂ Y (y ⟼ (Iscontr₁ (Hfiber₁ X₁ Y₁ f₁ y)), y ⟼ (Iscontr₂ (Hfiber₂ X Y f y))))).

Definition Weq { ⊢ X Y Type } ⊢ Σ f:X⟶Y, Isweq₁[X,Y,f] Type 

   ::= (_,X ⟼ Y ⟼ (Σ_istype₂ (pi1₂ X Y) (f ⟼ (Isweq₁ X₁ Y₁ f), f ⟼ (Isweq₂ X Y f)))).

Definition Isaprop { ⊢ X Type } ⊢ ∏ x:X, ∏ x':X, Iscontr₁[x=x'] Type

   := (_,X ⟾ pi₂[X, (x ⟾ @[∏](X₁, (x' ⟾ Iscontr₁ [ x=x' ])), 
   		       x ⟾ pi₂[X, (x' ⟾ Iscontr₁[ x₁=x'],
		       		    x' ⟾ Iscontr₂[Id_istype₂[X,x,x']])])]).

Definition Isaset { ⊢ X Type } ⊢ ∏ x:X, ∏ x':X, Isaprop₁[x=x'] Type

   ::= (_,X ⟼ (pi₂ X (x ⟼ (pi₁ X₁ (x' ⟼ (Isaprop₁ (Id_istype₁ X₁ x x')))), 
   		       x ⟼ (pi₂ X (x' ⟼ (Isaprop₁ (Id_istype₁ X₁ x₁ x')),
		       		    x' ⟼ (Isaprop₂ (Id_istype₂ X x x'))))))).

Definition idfun { ⊢ X Type } ⊢ λ x:X, x : X⟶X

   ::= (_,X ⟼ (lambda1₂ X X (x ⟼ x,x ⟼ x))).

#Theorem idisweq { ⊢ X Type } : @[Isweq](X,X,@[idfun](X)) 
#   ::= _  .

#   Local Variables:
#   compile-command: "make -C .. rules7 "
#   End:
