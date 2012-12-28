# pi1-relative binding

Check : LF (pi:texp) ** istype pi.

Check : LF (T:texp) ** istype T |= (U:texp) ** istype U |= (t:oexp) ** hastype t T |= (pi:texp) ** istype pi.

Check : LF (T:texp) -> ( (x:oexp) ** hastype x T |= (U:texp) ** istype U ).

Check : LF (T:texp) -> ( ((x:oexp) ** hastype x T |= (U:texp) ** istype U) |= (pi:texp) ** istype pi ).

Check : LF (T:texp) ** istype T |= ((x:oexp) ** hastype x T |= (U:texp) ** istype U) |= (pi:texp) ** istype pi.

Check : LF (T:texp) ** istype T |= ((x:oexp) ** hastype x T |= (y:oexp) ** hastype y T |= (U:texp) ** istype U) |= (pi:texp) ** istype pi.

#   Local Variables:
#   compile-command: "make -C .. run5 "
#   End:
