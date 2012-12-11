(** Hash codes, independent of variable names. *)

open Variables
open Typesystem

(* provisional and unused *)

let uhash = function
  | U_next -> 4483
  | U_max -> 45755

let thash = function
  | T_El -> 45 | T_U -> 55 | T_Pi -> 561 | T_Sigma -> 667 | T_Pt -> 5461 | T_Coprod -> 67
  | T_Coprod2 -> 121 | T_Empty -> 33 | T_IP -> 47 | T_Id -> 5867

let ohash = function
  | O_u -> 347 | O_j -> 587 | O_ev -> 689 | O_lambda -> 123 | O_forall -> 4345
  | O_pair -> 345 | O_pr1 -> 101 | O_pr2 -> 103 | O_total -> 107 | O_pt -> 109
  | O_pt_r -> 345 | O_tt -> 345 | O_coprod -> 2345 | O_ii1 -> 457 | O_ii2 -> 9218
  | O_sum -> 47 | O_empty -> 465 | O_empty_r -> 7456 | O_c -> 473 | O_ip_r -> 347
  | O_ip -> 3841 | O_paths -> 3845  | O_refl -> 376 | O_J -> 77 | O_rr0 -> 91
  | O_rr1 -> 97

let tachash = function
  | Tactic_name _ -> 1233		(* ?? *)
  | Tactic_index n -> 55 * n
  | Tactic_hole n -> 5 + n

let hhash = function
  | TAC tac -> tachash tac
  | U h -> uhash h
  | T h -> thash h
  | O h -> ohash h
  | V h -> 2

let rec chash = function
  | PAIR(_,x,y) -> 611 * chash x + 711 * chash y
  | LAMBDA(_,body) -> chash body
  | CAN e -> ahash e
and spine_hash = function
  | NIL -> 1
  | FST r -> 123 + spine_hash r
  | SND r -> 13 + spine_hash r
  | ARG(c,r) -> chash c + 2345 * (spine_hash r)
and ahash = function
  | (pos,APPLY(h,args)) -> hhash h + spine_hash args
