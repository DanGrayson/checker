# -*- coding: utf-8 -*-

# the "|-" operator is not fully implemented yet

Verify LF pi Type;;

Verify LF T Type |- U Type |- t::T |- pi Type;;

Verify LF (T:texp) -> ( x::T |- U Type );;

Verify LF (T:texp) -> ( x::T |- pi Type );;

Verify LF T Type |- ( x::T |- U Type) |- pi Type;;

Verify { ⊢ T Type } { t : T ⊢ U Type } ⊢ @∏[T,t.U[t]] Type;;

Verify LF T Type |- ( x::T |- y::T |- U Type) |- pi Type;;

#   Local Variables:
#   compile-command: "make -C .. theorem-binders "
#   End:
