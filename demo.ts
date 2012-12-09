# -*- coding: utf-8 -*-

Check LF ev_hastype.

Define compose (T U V:Type) (g:U⟶V) (f:T⟶U) (t:T) := [ev;_](g,[ev;_](f,t,U),V) : V ;; (
       ev_hastype U (_ ⟼ V) g ([ev] f t (_ ⟼ U)) $a ( 
       ev_hastype T (_ ⟼ U) f t $a $a 
       ))  .

Check LF λ_hastype.

Define compose1 (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;;
      # LF syntax
      (λ_hastype
       T
       >V
       (t ⟼ ([ev] g ([ev] f t >U) >V) ) 
       $a 
       (t ⟼ t_has_type_T ⟼ 
       	  ( ev_hastype U >V g ([ev] f t >U) $a ( ev_hastype T >U f t $a $a )))).

Define compose2 (T U V:Type) (g:U⟶V) (f:T⟶U) := [lambda;t](T,[ev;_](g,[ev;_](f,t,U),V)) : T ⟶ V ;
      # improved TS syntax
      λ_hastype
       T
       (_ ⟾ V)
       (t ⟾ g (f t) ) 
       $a 
       (t  ⟾  h  ⟾  
        ev_hastype U (_ ⟾ V) g (f t) $a ( ev_hastype T (_ ⟾ U) f t $a $a )).

Define A (u : Ulevel; u=u) (t : [U](u)) := [El](t); (El_type u $assumption $0).

Define B (u : Ulevel) (t : [U](u)) := [El](t); (El_type u $a $0).

Variable u1 : Ulevel.

Define C := [u](u1) : [U]([next](u1)); (u_univ $a).

Check LF (B ([next] u1) ([u] u1) (u_univ u1)).

Check LF ∏_istype.

Define E (u1 u2 u3:Ulevel)(K:Type) := K⟶K; (∏_istype $a >$a >>$a ) .

#   Local Variables:
#   compile-command: "make demo "
#   End:
