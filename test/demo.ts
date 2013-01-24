# -*- coding: utf-8 -*-

Check LF : oexp -> oexp.
Check LF : (t:texp) -> istype t.
Include "rules/TS0.ts".
Check LF ∏_istype.

# the subordination checker will give an error on this:
# Check LF : (t:texp) -> istype t -> oexp.

# Theorem pathcomp { |- T Type, a b c : T, f : a=b, g : b=c } : a=c := _.

#   Local Variables:
#   compile-command: "make -C .. demo "
#   End:
