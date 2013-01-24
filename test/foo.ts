# -*- coding: utf-8 -*-

Include "rules/TS7.ts".
Check LF cast.

# This is wrong:
#    cast : (T:texp) ⟶ (U:texp) ⟶ tequal T U ⟶ (o:oexp) ⟶ (x:Singleton(o : oexp)) × istype T ⟶ istype U ⟶ hastype o T ⟶ hastype x U

End.							   # we need to fix the encoding of "cast"

#   Local Variables:
#   compile-command: "make -C .. foo "
#   End:
