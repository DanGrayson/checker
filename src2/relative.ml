(** Handling relative indices. *)

open Expressions

let rec map_expr_list_limit f limit s = match s with
  | ARG(i,x,a) -> 
      let limit = limit + i in
      let x' = f limit x in 
      let a' = map_expr_list_limit f limit a in 
      if x' == x && a' == a then s else ARG(i,x',a')
  | END -> s

let rec rel_shift_expr shift limit e =
  if shift = 0 then e else
  match e with
  | BASIC(h,args) ->
      let args' = map_expr_list_limit (rel_shift_expr shift) limit args in
      let h' = rel_shift_head shift limit h in
      if h' == h && args' == args then e else BASIC(h',args')

and rel_shift_head shift limit h = 
  match h with
  | Var (Rel i) when i >= limit -> Var (Rel (shift+i))
  | _ -> h

and rel_shift_jgmt shift limit j =
  match j with
  | J_Pi(a,b) ->
      let a' = rel_shift_jgmt shift limit a in
      let limit = limit + 1 in
      let b' = rel_shift_jgmt shift limit b in
      if a' == a && b' == b then j else J_Pi(a',b')
  | J_istype(None) -> j
  | J_istype(Some t) ->
      let t' = rel_shift_expr shift limit t in
      if t == t' then j else J_istype(Some t')
  | J_hastype(t,None) ->
      let t' = rel_shift_expr shift limit t in
      if t == t' then j else J_hastype(t',None)
  | J_hastype(t,Some o) ->
      let t' = rel_shift_expr shift limit t in
      let o' = rel_shift_expr shift limit o in
      if t == t' && o == o' then j else J_hastype(t',Some o')
  | J_type_equality(t,u,None) ->
      let t' = rel_shift_expr shift limit t in
      let u' = rel_shift_expr shift limit u in
      if t == t' && u == u' then j else J_type_equality(t',u',None)
  | J_type_equality(t,u,Some o) ->
      let t' = rel_shift_expr shift limit t in
      let u' = rel_shift_expr shift limit u in
      let o' = rel_shift_expr shift limit o in
      if t == t' && u == u' && o == o' then j else J_type_equality(t',u',Some o')
  | J_object_equality(t,n,o,None) ->
      let t' = rel_shift_expr shift limit t in
      let n' = rel_shift_expr shift limit n in
      let o' = rel_shift_expr shift limit o in
      if t == t' && n == n' && o == o' then j else J_object_equality(t',n',o',None)
  | J_object_equality(t,n,o,Some p) ->
      let t' = rel_shift_expr shift limit t in
      let n' = rel_shift_expr shift limit n in
      let o' = rel_shift_expr shift limit o in
      let p' = rel_shift_expr shift limit p in
      if t == t' && n == n' && o == o' && p == p' then j else J_object_equality(t',n',o',Some p')

let rel_shift_expr shift e = if shift = 0 then e else rel_shift_expr 0 shift e

let rel_shift_head shift h = if shift = 0 then h else rel_shift_head 0 shift h

let rel_shift_jgmt shift t = if shift = 0 then t else rel_shift_jgmt 0 shift t
