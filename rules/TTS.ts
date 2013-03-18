# -*- mode: ts; coding: utf-8 -*-

Mode TTS.

Axiom Wrefl { ⊢ T U Type } [ T ~ U Type ] [ @Wrefl : T ≡ U ].

Axiom Wsymm { ⊢ T U Type, p : T ≡ U } [ @Wsymm[p] : U ≡ T ].

Axiom Wtrans { ⊢ T U V Type, p12 : T ≡ U, p23: U ≡ V } [ @Wtrans[p12,p23,U] : T ≡ V ].

Axiom wrefl { ⊢ T Type, p : o : T, p' : o' : T } [ o ~ o' : T ] [ @wrefl[p,p'] : o ≡ o' : T ].

Axiom wsymm { ⊢ T Type } (o:oexp) ⇒ (o':oexp) ⇒ { ⊢ q : o ≡ o' : T } [ @wsymm[q] : o' ≡ o : T ].

# this just displays an alternative possibility, in case we would prefer to write @wsymm[p,p',q]:
Axiom wsymm' { ⊢ T Type, p : o : T, p' : o' : T, q : o ≡ o' : T } [ @wsymm[q] : o' ≡ o : T ]. 

Axiom wtrans { ⊢ T Type } (o1:oexp) ⇒ (o2:oexp) ⇒ (o3:oexp) ⇒ { ⊢ p12 : o1 ≡ o2 : T, p23 : o2 ≡ o3 : T } [ @wtrans[p12,p23,o2] : o1 ≡ o3 : T ].

Check LF wtrans.

Axiom WEl { ⊢ p : o : @U } [ @El[o,p] Type ].

# End.

# # translate a binder "{ |- px : x : T } ... " into "(px:wexp) -> (x:oexp) -> (w_hastype px x T) -> ..."

# Axiom 7 orefl { ⊢ T Type, px : x : T, py : y : T } [ x ~ y : T ] ⇒ [ @wrefl[px,py] : x ≡ y : T ].

# End.

# Axiom 3.4.11 oeqsymm { ⊢ T Type, x : T, y : T } [ x ≡ y : T ] ⇒ [ y ≡ x : T ].

# Axiom 3.4.12 oeqtrans { ⊢ T Type, x : T, y : T, z : T } [ x ≡ y : T ]
#       	⇒ [ y ≡ z : T ] ⇒ [ x ≡ z : T ].


#   Local Variables:
#   compile-command: "make -C .. TTS "
#   End:
