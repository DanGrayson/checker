(*
  This code is in the public domain, and comes from a post at

  http://lambda-the-ultimate.org/node/1920#comment-23346

  by Neelakantan R. Krishnaswami whose home page is at

  http://www.cs.cmu.edu/~neelk/

*)

type var = string

type sexp =
  | Bool of bool
  | Sym of string
  | Lambda of var list * sexp
  | Var of var
  | If of sexp * sexp * sexp
  | Cons of sexp * sexp
  | Car of sexp
  | Cdr of sexp
  | SetCar of sexp * sexp
  | SetCdr of sexp * sexp
  | App of sexp * sexp list
  | Set of var * sexp
  | LetCC of var * sexp
  | Throw of sexp * sexp

type frametype = FCons | FSetCar | FSetCdr | FThrow

type env = (var * value ref) list
and value =
  | Symbol of string
  | Boolean of bool
  | Fun of env * var list * sexp
  | Pair of value ref * value ref
  | Cont of env * cont
and cont = frame list
and frame =
  | IfK of sexp * sexp
  | K1 of frametype * sexp
  | K2 of frametype * value
  | CarK
  | CdrK
  | AppK1 of sexp list
  | AppK2 of value * (value ref) list * sexp list
  | SetK of var

let undef = Symbol "undefined"

let find r x = List.assoc x r

let rec eval e r k =
  match e with
  | Bool b ->         throw (Boolean b) r k
  | Sym s ->          throw (Symbol s) r k
  | Lambda(x, e) ->   throw (Fun(r, x, e)) r k
  | Var x ->          throw !(find r x) r k
  | If(e, e1, e2) ->  eval e r (IfK(e1, e2) :: k)
  | Cons(e1, e2) ->   eval e1 r (K1(FCons, e2) :: k)
  | Car e ->          eval e r (CarK :: k)
  | Cdr e ->          eval e r (CdrK :: k)
  | SetCar(e1, e2) -> eval e1 r (K1(FSetCar, e2) :: k)
  | SetCdr(e1, e2) -> eval e1 r (K1(FSetCdr, e2) :: k)
  | App(f, args) ->   eval f r (AppK1(args) :: k)
  | Set(x, e) ->      eval e r (SetK(x) :: k)
  | LetCC(x, e) ->    eval e ((x, ref (Cont(r, k))) :: r) k
  | Throw(e1, e2) ->  eval e1 r (K1(FThrow, e2) :: k)
and throw v r k =
  match v, k with
  | v, [] ->                                  v
  | v, (K1(ftype, e) :: k) ->                 eval e r (K2(ftype, v) :: k)
  | (Boolean b), (IfK(e1, e2) :: k) ->        eval (if b then e1 else e2) r k
  | v, (K2(FCons, fst) :: k) ->               throw (Pair(ref fst, ref v)) r k
  | v, (K2(FSetCar, Pair(r1, r2)) :: k) ->    (r1 := v; throw undef r k)
  | v, (K2(FSetCdr, Pair(r1, r2)) :: k) ->    (r2 := v; throw undef r k)
  | Cont(r, k), (K2(FThrow, v) :: _) ->       throw v r k
  | v, (SetK(x) :: k) ->                      ((find r x) := v; throw undef r k)
  | (Pair(fst, snd)), (CarK :: k) ->          throw !fst r k
  | (Pair(fst, snd)), (CdrK :: k) ->          throw !snd r k
  | Fun(r, [], e), (AppK1([]) :: k) ->        eval e r k
  | v, (AppK1(arg :: args) :: k) ->           eval arg r (AppK2(v, [], args) :: k)
  | v, (AppK2(f, vs, e :: es) :: k) ->        eval e r (AppK2(f, (ref v) :: vs, es) :: k)
  | Fun(r, xs, e), (AppK2(f, vs, []) :: k) -> let r = (List.combine xs (List.rev vs)) @ r in eval e r k
  | _ ->                                      failwith "Helpful Error Message"
