(** Handling relative indices. *)

open Judgments

let rec map_expr_list f s = match s with
  | ARG(x,a) -> let x' = f x in let a' = map_expr_list f a in if x' == x && a' == a then s else ARG(x',a')
  | FST a -> let a' = map_expr_list f a in if a' == a then s else FST(a')
  | SND a -> let a' = map_expr_list f a in if a' == a then s else SND(a')
  | END -> s

let rec rel_shift_expr limit shift e =
  if shift = 0 then e else
  match unmark e with
  | BASIC(h,args) ->
      let args' = map_expr_list (rel_shift_expr limit shift) args in
      let h' = rel_shift_head limit shift h in
      if h' == h && args' == args then e else get_pos e, BASIC(h',args')
  | PAIR(x,y) ->
      let x' = rel_shift_expr limit shift x in
      let y' = rel_shift_expr limit shift y in
      if x' == x && y' == y then e else get_pos e, PAIR(x',y')
  | TEMPLATE(v, body) ->
      let limit = limit + 1 in
      let body' = rel_shift_expr limit shift body in
      if body' == body then e else get_pos e, TEMPLATE(v, body')

and rel_shift_head limit shift h = 
  match h with
  | V (Rel i) when i >= limit -> V (Rel (shift+i))
  | _ -> h

and rel_shift_type limit shift t =
  match unmark t with
  | J_Pi(v,a,b) ->
      let a' = rel_shift_type limit shift a in
      let limit = limit + 1 in
      let b' = rel_shift_type limit shift b in
      if a' == a && b' == b then t else get_pos t, J_Pi(v,a',b')
  | J_Sigma(v,a,b) ->
      let a' = rel_shift_type limit shift a in
      let limit = limit + 1 in
      let b' = rel_shift_type limit shift b in
      if a' == a && b' == b then t else get_pos t, J_Sigma(v,a',b')
  | J_Basic(label,args) ->
      let args' = List.map (rel_shift_expr limit shift) args in
      if args' == args then t else get_pos t, J_Basic(label, args')
  | J_Singleton(e,u) ->
      let e' = rel_shift_expr limit shift e in
      let u' = rel_shift_type limit shift u in
      if e' == e && u' == u then t else get_pos t, J_Singleton(e',u')

let rel_shift_expr shift e = if shift = 0 then e else rel_shift_expr 0 shift e

let rel_shift_head shift h = if shift = 0 then h else rel_shift_head 0 shift h

let rel_shift_type shift t = if shift = 0 then t else rel_shift_type 0 shift t
