# -*- coding: utf-8 -*-

# fix interpretation of "cast"

Mode Pairs.
Include "rules/TS0.ts".
Check LF ∏_istype.
Check LF λ_hastype.
Check LF ev_hastype.
Clear.
Mode Relative.
Include "rules/TS0.ts".
Check LF ∏_istype.
Check LF λ_hastype.
Check LF ev_hastype.
Clear.
End.
Mode Simple.
Include "rules/TS0.ts".
Check LF cast.

#   Local Variables:
#   compile-command: "make -C .. foo "
#   End:
