# -*- coding: utf-8 -*-

Check LF : oexp -> oexp.
Check LF : (t:texp) -> istype t.

# the subordination checker will give an error on this:
 Check LF : (t:texp) -> istype t -> oexp.

Mode Relative.
Include "rules/TS0.ts".
Check LF ∏_istype.					    # oops, is normalization right?  is printing working?
Clear.

Mode Pairs.
Include "rules/TS0.ts".
Check LF ∏_istype.
End.


#   Local Variables:
#   compile-command: "make -C .. demo "
#   End:
