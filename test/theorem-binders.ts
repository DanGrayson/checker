# -*- coding: utf-8 -*-

# the "|-" operator is not fully implemented yet

Check LF : pi Type..

Check LF : T Type |- U Type |- t::T |- pi Type..

Check LF : (T:texp) -> ( x::T |- U Type )..

Check LF : (T:texp) -> ( x::T |- pi Type )..

Check LF : T Type |- ( x::T |- U Type) |- pi Type..

Check TS : { ⊢ T Type } { t : T ⊢ U Type } ⊢ @∏[T,t.U[t]] Type..

Check LF : T Type |- ( x::T |- y::T |- U Type) |- pi Type..

#   Local Variables:
#   compile-command: "make -C .. theorem-binders "
#   End:
