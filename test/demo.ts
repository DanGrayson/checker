# -*- coding: utf-8 -*-

Check LF : oexp -> oexp.
Check LF : (t:texp) -> istype t.

Mode Relative.
Include "rules/TS0.ts".
Check LF ∏_istype.
Clear.

Mode Pairs.
Include "rules/TS0.ts".
Check LF ∏_istype.
End.

# the subordination checker will give an error on this:
# Check LF : (t:texp) -> istype t -> oexp.

#   Local Variables:
#   compile-command: "make -C .. demo "
#   End:
