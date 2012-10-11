(*

  This code is in the public domain, and is based on a post at

  http://lambda-the-ultimate.org/node/1920#comment-23346

  by Neelakantan R. Krishnaswami whose home page is at

  http://www.cs.cmu.edu/~neelk/

*)

type variable = string

type expr =
  | BooleanS of bool
  | SymbolS of string
  | Function of variable list * expr
  | Variable of variable
  | If of expr * expr * expr
  | Cons of expr * expr
  | Car of expr
  | Cdr of expr
  | SetCar of expr * expr
  | SetCdr of expr * expr
  | Apply of expr * expr list
  | Set of variable * expr
  | LetCC of variable * expr
  | Throw of expr * expr
  | NilS

type bindings = (variable * value ref) list
and value =
  | NilV
  | SymbolV of string
  | BooleanV of bool
  | ConsCell of value ref * value ref
  | FuncClosure of bindings * variable list * expr
  | ContClosure of bindings * continuation
and continuation = frame list
and frame =
  | IfK of expr * expr
  | ConsK1 of expr | ConsK2 of value
  | SetCarK1 of expr | SetCarK2 of value
  | SetCdrK1 of expr | SetCdrK2 of value
  | ThrowK1 of expr | ThrowK2 of value
  | CarK
  | CdrK
  | ApplyK1 of expr list
  | ApplyK2 of value * (value ref) list * expr list
  | SetK of variable

let rec eval e r k =
  match e with
  | NilS ->           throw NilV r k
  | BooleanS b ->     throw (BooleanV b) r k
  | SymbolS s ->      throw (SymbolV s) r k
  | Function(x, e) -> throw (FuncClosure(r, x, e)) r k
  | Variable x ->     throw !(List.assoc x r) r k
  | If(e, e1, e2) ->  eval e r (IfK(e1, e2) :: k)
  | Cons(e1, e2) ->   eval e1 r (ConsK1 e2 :: k)
  | Car e ->          eval e r (CarK :: k)
  | Cdr e ->          eval e r (CdrK :: k)
  | SetCar(e1, e2) -> eval e1 r (SetCarK1 e2 :: k)
  | SetCdr(e1, e2) -> eval e1 r (SetCdrK1 e2 :: k)
  | Apply(f, args) -> eval f r (ApplyK1 args :: k)
  | Set(x, e) ->      eval e r (SetK x :: k)
  | LetCC(x, e) ->    eval e ((x, ref (ContClosure(r, k))) :: r) k
  | Throw(e1, e2) ->  eval e1 r (ThrowK1 e2 :: k)
and throw v r k =
  match v, k with
  | v, [] ->                                          v

  | v, (ConsK1 e :: k) ->                             eval e r (ConsK2 v :: k)
  | v, (ConsK2 car :: k) ->                           throw (ConsCell(ref car, ref v)) r k

  | v, (SetCarK1 e :: k) ->                           eval e r (SetCarK2 v :: k)
  | v, (SetCarK2 ConsCell(r1, r2) :: k) ->            (r1 := v; throw NilV r k)
  | v, (SetCarK2 _ :: k) ->                           failwith "setcar expected a cons cell"

  | v, (SetCdrK1 e :: k) ->                           eval e r (SetCdrK2 v :: k)
  | v, (SetCdrK2 ConsCell(r1, r2) :: k) ->            (r2 := v; throw NilV r k)
  | v, (SetCdrK2 _ :: k) ->                           failwith "setcdr expected a cons cell"

  | v, (ThrowK1 e :: k) ->                            eval e r (ThrowK2 v :: k)
  | ContClosure(r, k), (ThrowK2 v :: _) ->            throw v r k

  | (ConsCell(car, cdr)), (CarK :: k) ->              throw !car r k
  | (ConsCell(car, cdr)), (CdrK :: k) ->              throw !cdr r k

  | v, (ApplyK1(arg :: rest) :: k) ->                 eval arg r (ApplyK2(v, [], rest) :: k)
  | FuncClosure(r, [], e), (ApplyK1 [] :: k) ->       eval e r k
  | v, (ApplyK2(f, vs, e :: es) :: k) ->              eval e r (ApplyK2(f, (ref v) :: vs, es) :: k)
  | FuncClosure(r, xs, e), (ApplyK2(f, vs, []) :: k) ->   eval e ((List.combine xs (List.rev vs)) @ r) k

  | (BooleanV b), (IfK(e1, e2) :: k) ->               eval (if b then e1 else e2) r k

  | v, (SetK(x) :: k) ->                              ((List.assoc x r) := v; throw NilV r k)

  | _ ->                                              failwith "internal error"
