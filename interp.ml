(*
  This code is in the public domain, and comes from a post at

  http://lambda-the-ultimate.org/node/1920#comment-23346

  by Neelakantan R. Krishnaswami whose home page is at

  http://www.cs.cmu.edu/~neelk/

*)

type var = string

type sexp =
  | BooleanS of bool
  | SymbolS of string
  | Lambda of var list * sexp
  | Var of var
  | If of sexp * sexp * sexp
  | Cons of sexp * sexp
  | Car of sexp
  | Cdr of sexp
  | SetCar of sexp * sexp
  | SetCdr of sexp * sexp
  | Apply of sexp * sexp list
  | Set of var * sexp
  | LetCC of var * sexp
  | Throw of sexp * sexp
  | NilS

type bindings = (var * value ref) list
and value =
  | SymbolV of string
  | BooleanV of bool
  | Closure of bindings * var list * sexp
  | ConsCell of value ref * value ref
  | Cont of bindings * cont
  | NilV
and cont = frame list
and frame =
  | IfK of sexp * sexp
  | ConsK1 of sexp | ConsK2 of value
  | SetCarK1 of sexp | SetCarK2 of value
  | SetCdrK1 of sexp | SetCdrK2 of value
  | ThrowK1 of sexp | ThrowK2 of value
  | CarK
  | CdrK
  | ApplyK1 of sexp list
  | ApplyK2 of value * (value ref) list * sexp list
  | SetK of var

let rec eval e r k =
  match e with
  | NilS ->           throw NilV r k
  | BooleanS b ->     throw (BooleanV b) r k
  | SymbolS s ->      throw (SymbolV s) r k
  | Lambda(x, e) ->   throw (Closure(r, x, e)) r k
  | Var x ->          throw !(List.assoc x r) r k
  | If(e, e1, e2) ->  eval e r (IfK(e1, e2) :: k)
  | Cons(e1, e2) ->   eval e1 r (ConsK1 e2 :: k)
  | Car e ->          eval e r (CarK :: k)
  | Cdr e ->          eval e r (CdrK :: k)
  | SetCar(e1, e2) -> eval e1 r (SetCarK1 e2 :: k)
  | SetCdr(e1, e2) -> eval e1 r (SetCdrK1 e2 :: k)
  | Apply(f, args) -> eval f r (ApplyK1 args :: k)
  | Set(x, e) ->      eval e r (SetK x :: k)
  | LetCC(x, e) ->    eval e ((x, ref (Cont(r, k))) :: r) k
  | Throw(e1, e2) ->  eval e1 r (ThrowK1 e2 :: k)
and throw v r k =
  match v, k with
  | v, [] ->                                          v
  | v, (ConsK1 e :: k) ->                             eval e r (ConsK2 v :: k)
  | v, (SetCarK1 e :: k) ->                           eval e r (SetCarK2 v :: k)
  | v, (SetCdrK1 e :: k) ->                           eval e r (SetCdrK2 v :: k)
  | v, (ThrowK1 e :: k) ->                            eval e r (ThrowK2 v :: k)
  | (BooleanV b), (IfK(e1, e2) :: k) ->               eval (if b then e1 else e2) r k
  | v, (ConsK2 car :: k) ->                           throw (ConsCell(ref car, ref v)) r k
  | v, (SetCarK2 ConsCell(r1, r2) :: k) ->            (r1 := v; throw NilV r k)
  | v, (SetCdrK2 ConsCell(r1, r2) :: k) ->            (r2 := v; throw NilV r k)
  | Cont(r, k), (ThrowK2 v :: _) ->                   throw v r k
  | v, (SetK(x) :: k) ->                              ((List.assoc x r) := v; throw NilV r k)
  | (ConsCell(car, cdr)), (CarK :: k) ->              throw !car r k
  | (ConsCell(car, cdr)), (CdrK :: k) ->              throw !cdr r k
  | Closure(r, [], e), (ApplyK1 [] :: k) ->           eval e r k
  | v, (ApplyK1(arg :: rest) :: k) ->                 eval arg r (ApplyK2(v, [], rest) :: k)
  | v, (ApplyK2(f, vs, e :: es) :: k) ->              eval e r (ApplyK2(f, (ref v) :: vs, es) :: k)
  | Closure(r, xs, e), (ApplyK2(f, vs, []) :: k) ->   eval e ((List.combine xs (List.rev vs)) @ r) k
  | _ ->                                              failwith "internal error"
