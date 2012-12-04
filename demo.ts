# -*- coding: utf-8 -*-

# Check LF El_type.

Define A (u : Ulevel) (t : [U](u)) := *t; (El_type u t h$1).

Define B (u : Ulevel) (t : [U](u)) := *t; (El_type $a $a $a).

Define C (u : Ulevel) (t : [U](u)) := *t; (El_type $2 $2 $2).

# Show.

#   Local Variables:
#   compile-command: "make demo "
#   End:
