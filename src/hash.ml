(** Hash codes, independent of variable names. *)

open Typesystem

(* provisional and unused *)

let uhash = function
  | U_next -> 4483
  | U_max -> 45755

let thash = function
  | T_El -> 45 | T_U -> 55 | T_U' -> 551 | T_Pi -> 561 | T_Sigma -> 667 | T_Pt -> 5461 | T_Coprod -> 67
  | T_Coprod2 -> 121 | T_Empty -> 33 | T_IP -> 47 | T_Id -> 5867

let ohash = function
  | O_u -> 347 | O_j -> 587 | O_ev -> 689 | O_lambda -> 123 | O_forall -> 4345
  | O_pair -> 345 | O_pr1 -> 101 | O_pr2 -> 103 | O_total -> 107 | O_pt -> 109
  | O_pt_r -> 345 | O_tt -> 345 | O_coprod -> 2345 | O_ii1 -> 457 | O_ii2 -> 9218
  | O_sum -> 47 | O_empty -> 465 | O_empty_r -> 7456 | O_c -> 473 | O_ip_r -> 347
  | O_ip -> 3841 | O_paths -> 3845  | O_refl -> 376 | O_J -> 77 | O_rr0 -> 91
  | O_rr1 -> 97 | O_nat -> 971 | O_nat_r -> 972 | O_O -> 973 | O_S -> 974

let whash = function
  | W_Wrefl -> 1233
  | W_Wsymm -> 1232
  | W_Wtrans -> 1231
  | W_wrefl -> 1230
  | W_wsymm -> 1229
  | W_wtrans -> 1228
  | W_wconv -> 1227
  | W_wconveq -> 1226
  | W_weleq -> 1225
  | W_wpi1 -> 1224
  | W_wpi2 -> 1223
  | W_wlam -> 1222
  | W_wl1 -> 129
  | W_wl2 -> 128
  | W_wev -> 127
  | W_wevt1 -> 126
  | W_wevt2 -> 125
  | W_wevf -> 124
  | W_wevo -> 123
  | W_wbeta -> 122
  | W_weta -> 121
  | W_QED -> 148

let tachash = function
  | _ -> 1233

let rec hhash = function
  | TACTIC tac -> tachash tac
  | W h -> whash h
  | U h -> uhash h
  | T h -> thash h
  | O h -> ohash h
  | V h -> 2

and expr_hash e = match Error.unmark e with
  | PAIR(x,y) -> 611 * expr_hash x + 711 * expr_hash y
  | TEMPLATE(_,body) -> expr_hash body
  | BASIC(h,args) -> hhash h + expr_list_hash args

and type_hash t = raise Error.NotImplemented

and expr_list_hash = function
  | END -> 1
  | FST r -> 123 + expr_list_hash r
  | SND r -> 13 + expr_list_hash r
  | ARG(c,r) -> expr_hash c + 2345 * (expr_list_hash r)
