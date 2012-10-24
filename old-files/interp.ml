(*

  This code is in the public domain, and is based on a post at

  http://lambda-the-ultimate.org/node/1920#comment-23346

  by Neelakantan R. Krishnaswami whose home page is at

  http://www.cs.cmu.edu/~neelk/

*)

exception NotImplemented

type variable = string

type expr =
  | BooleanS of bool
  | IntegerS of int
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
  | IntegerV of int
  | ConsCell of value ref * value ref
  | FuncClosure of bindings * variable list * expr
  | ContClosure of bindings * continuations
and continuations = continuation list
and continuation =
  | IfCont of expr * expr
  | ConsCont1 of expr | ConsCont2 of value
  | SetCarCont1 of expr | SetCarCont2 of value
  | SetCdrCont1 of expr | SetCdrCont2 of value
  | ThrowCont1 of expr | ThrowCont2 of value
  | CarCont
  | CdrCont
  | ApplyCont1 of expr list
  | ApplyCont2 of value * (value ref) list * expr list
  | SetCont of variable

let rec eval e r k =
  match e with
  | NilS ->           continue NilV r k
  | BooleanS b ->     continue (BooleanV b) r k
  | IntegerS b ->     continue (IntegerV b) r k
  | SymbolS s ->      continue (SymbolV s) r k
  | Function(x, e) -> continue (FuncClosure(r, x, e)) r k
  | Variable x ->     continue !(try List.assoc x r with Not_found -> (Printf.printf "unset variable: %s\n" x; raise Not_found)) r k
  | If(e, e1, e2) ->  eval e r (IfCont(e1, e2) :: k)
  | Cons(e1, e2) ->   eval e1 r (ConsCont1 e2 :: k)
  | Car e ->          eval e r (CarCont :: k)
  | Cdr e ->          eval e r (CdrCont :: k)
  | SetCar(e1, e2) -> eval e1 r (SetCarCont1 e2 :: k)
  | SetCdr(e1, e2) -> eval e1 r (SetCdrCont1 e2 :: k)
  | Apply(f, args) -> eval f r (ApplyCont1 args :: k)
  | Set(x, e) ->      eval e r (SetCont x :: k)
  | LetCC(x, e) ->    eval e ((x, ref (ContClosure(r, k))) :: r) k
  | Throw(e1, e2) ->  eval e1 r (ThrowCont1 e2 :: k)
and continue v r k =
  match v, k with
  | v, [] ->                                          v

  | v, (ConsCont1 e :: k) ->                             eval e r (ConsCont2 v :: k)
  | v, (ConsCont2 car :: k) ->                           continue (ConsCell(ref car, ref v)) r k

  | v, (SetCarCont1 e :: k) ->                           eval e r (SetCarCont2 v :: k)
  | v, (SetCarCont2 ConsCell(r1, r2) :: k) ->            (r1 := v; continue NilV r k)
  | v, (SetCarCont2 _ :: k) ->                           failwith "setcar expected a cons cell"

  | v, (SetCdrCont1 e :: k) ->                           eval e r (SetCdrCont2 v :: k)
  | v, (SetCdrCont2 ConsCell(r1, r2) :: k) ->            (r2 := v; continue NilV r k)
  | v, (SetCdrCont2 _ :: k) ->                           failwith "setcdr expected a cons cell"

  | v, (ThrowCont1 e :: k) ->                            eval e r (ThrowCont2 v :: k)
  | ContClosure(r, k), (ThrowCont2 v :: _) ->            continue v r k

  | (ConsCell(car, cdr)), (CarCont :: k) ->              continue !car r k
  | _, (CarCont :: k) ->                                 failwith "car: expected a cons cell"

  | (ConsCell(car, cdr)), (CdrCont :: k) ->              continue !cdr r k
  | _, (CdrCont :: k) ->                                 failwith "cdr: expected a cons cell"

  | f, (ApplyCont1(arg :: rest) :: k) ->                 eval arg r (ApplyCont2(f, [], rest) :: k)
  | FuncClosure(r, [], e), (ApplyCont1 [] :: k) ->       eval e r k
  | _, (ApplyCont1 [] :: k) ->                           failwith "apply: expected a function"

  | v, (ApplyCont2(f, vs, e :: es) :: k) ->              eval e r (ApplyCont2(f, (ref v) :: vs, es) :: k)
  | FuncClosure(r, xs, e), (ApplyCont2(f, vs, []) :: k) -> eval e ((List.combine xs (List.rev vs)) @ r) k
  | _, (ApplyCont2(f, vs, []) :: k) ->                   failwith "apply: expected a function"

  | (BooleanV b), (IfCont(e1, e2) :: k) ->               eval (if b then e1 else e2) r k

  | v, (SetCont(x) :: k) ->                              ((List.assoc x r) := v; continue NilV r k)

  | _ ->                                                 failwith "internal error"
