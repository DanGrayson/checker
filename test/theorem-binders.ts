# -*- coding: utf-8 -*-

# the "|-" operator is not fully implemented yet

Check Judgment LF pi Type;;

Check Judgment LF T Type |- U Type |- t::T |- pi Type;;

Check Judgment LF (T:texp) -> ( x::T |- U Type );;

Check Judgment LF (T:texp) -> ( x::T |- pi Type );;

Check Judgment LF T Type |- ( x::T |- U Type) |- pi Type;;

Check Judgment { ⊢ T Type } { t : T ⊢ U Type } ⊢ @∏[T,t.U[t]] Type;;

Check Judgment LF T Type |- ( x::T |- y::T |- U Type) |- pi Type;;

#   Local Variables:
#   compile-command: "make -C .. theorem-binders "
#   End:
