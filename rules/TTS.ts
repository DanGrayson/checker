# -*- mode: ts; coding: utf-8 -*-

Axiom 4 trefl { ⊢ T U Type } [ T ~ U Type ] [ @[Wrefl] : T ≡ U ].

Axiom 5 teqsymm { ⊢ T U Type } { ⊢ p : T ≡ U } [ @[Wsymm][p] : U ≡ T ].

Axiom 6 teqtrans { ⊢ T U V Type } { ⊢ p12 : T ≡ U } { ⊢ p23: U ≡ V } [ @[Wtrans][p12,p23,U] : T ≡ V ].

# End.

# # translate a binder "{ |- px : x : T } ... " into "(px:wexp) -> (x:oexp) -> (w_hastype px x T) -> ..."

# Axiom 7 orefl { ⊢ T Type, px : x : T, py : y : T } [ x ~ y : T ] ⇒ [ @[wrefl][px,py] : x ≡ y : T ].

# End.

# Axiom 3.4.11 oeqsymm { ⊢ T Type, x : T, y : T } [ x ≡ y : T ] ⇒ [ y ≡ x : T ].

# Axiom 3.4.12 oeqtrans { ⊢ T Type, x : T, y : T, z : T } [ x ≡ y : T ] 
#       	⇒ [ y ≡ z : T ] ⇒ [ x ≡ z : T ].


#   Local Variables:
#   compile-command: "make -C .. TTS "
#   End:
