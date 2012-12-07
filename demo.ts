# -*- coding: utf-8 -*-

Define A (u : Ulevel; u=u) (t : [U](u)) := [El](t); (El_type u t h$299).

Define B (u : Ulevel) (t : [U](u)) := [El](t); (El_type $2 $a $a).

Variable u1 : Ulevel.

Define C := [u](u1) : [U]([next](u1)); (u_univ $a).

Check LF (B ([next] u1) ([u] u1) (u_univ u1)).

Show 7.

#   Local Variables:
#   compile-command: "make demo "
#   End:
