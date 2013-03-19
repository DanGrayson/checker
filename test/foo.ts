# -*- coding: utf-8 -*-


# both of the following lines should give an erro
# Check LF : (t:texp) -> istype t -> oexp.
# Axiom foo { ⊢ T U Type } [ T ≡ U ] ⇒ { ⊢ o : T } ⊢ o : U.

Axiom foo1 { ⊢ T U Type } [ T ≡ U ] { ⊢ o : T } ⊢ o : U;;   # then fix cast this way
Axiom foo2 { ⊢ T U Type } { ⊢ o : T } [ T ≡ U ] ⊢ o : U;;   # then fix cast this way

Back 2;;


Include "rules/TS7.ts";;
Check LF cast;;

#   Local Variables:
#   compile-command: "make -C ;; foo "
#   End:
