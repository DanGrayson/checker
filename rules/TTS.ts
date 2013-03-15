# -*- mode: ts; coding: utf-8 -*-

Mode TTS.

Axiom 1.4 Wrefl { ⊢ T U Type } [ T ~ U Type ] [ @[Wrefl] : T ≡ U ].

Axiom 1.5 Wsymm { ⊢ T U Type } { ⊢ p : T ≡ U } [ @[Wsymm][p] : U ≡ T ].

Axiom 1.6 Wtrans { ⊢ T U V Type } { ⊢ p12 : T ≡ U } { ⊢ p23: U ≡ V } [ @[Wtrans][p12,p23,U] : T ≡ V ].

Axiom 1.7 wrefl { ⊢ T Type } { ⊢ p : o : T } { ⊢ p' : o' : T } [ o ~ o' : T ] [ @[wrefl][p,p'] : o ≡ o' : T ].

Check wrefl.

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
