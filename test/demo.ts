# -*- coding: utf-8 -*-

Check Judgment LF oexp -> oexp;;
Check Judgment LF (t:texp) -> istype t;;
Include "rules/TS0.ts";;
Check LF ∏_istype;;

# Theorem pathcomp { |- T Type, a b c : T, f : a=b, g : b=c } : a=c := _;;

#   Local Variables:
#   compile-command: "make -C .. demo "
#   End:
