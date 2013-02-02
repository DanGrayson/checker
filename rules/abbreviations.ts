# -*- coding: utf-8 -*-
# abbreviations for TS expressions 

Definition LF UU : uexp ⟶ texp := @[U].

Definition LF uu : uexp ⟶ oexp := @[u].

Definition LF jj : uexp ⟶ uexp ⟶ oexp := @[j].

Definition LF umax : uexp ⟶ uexp ⟶ uexp := @[max].

Definition LF next : uexp ⟶ uexp := @[next].

Definition LF Empty : texp := @[Empty].

Definition LF Pt : texp := @[Pt].

Definition LF pt : oexp := @[pt].

Definition LF tt : oexp := @[tt].

Definition LF El : oexp ⟶ texp := @[El].

Definition LF O : oexp := @[O].

Definition LF S : oexp := @[S].

#   Local Variables:
#   compile-command: "make -C .. abbreviations "
#   End:
