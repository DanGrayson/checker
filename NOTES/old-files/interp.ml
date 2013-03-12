(*

  This code is in the public domain, and is based on a post at

  http://lambda-the-ultimate.org/node/1920#comment-23346

  by Neelakantan R. Krishnaswami whose home page is at

  http://www.cs.cmu.edu/~neelk/

*)

type variable = string

type computation =
  | Value of value
  | Function of variable list * computation
  | Variable of variable
  | If of computation * computation * computation
  | Cons of computation * computation
  | Car of computation
  | Cdr of computation
  | SetCar of computation * computation
  | SetCdr of computation * computation
  | Apply of computation * computation list
  | Set of variable * computation
  | LetCC of variable * computation
  | Throw of computation * computation
and bindings = (variable * value ref) list
and value =
  | NilV
  | SymbolV of string
  | BooleanV of bool
  | IntegerV of int
  | ConsCell of value ref * value ref
  | FuncClosure of bindings * variable list * computation
  | ContClosure of bindings * continuation
and continuation = command list
and command =
  | IfCmd of computation * computation
  | ConsCmd1 of computation | ConsCmd2 of value
  | SetCarCmd1 of computation | SetCarCmd2 of value
  | SetCdrCmd1 of computation | SetCdrCmd2 of value
  | ThrowCmd1 of computation | ThrowCmd2 of value
  | CarCmd
  | CdrCmd
  | ApplyCmd1 of computation list
  | ApplyCmd2 of value * (value ref) list * computation list
  | SetCmd of variable

let rec eval e r k =
  match e with
  | Value v ->        continue v r k
  | Function(x, e) -> continue (FuncClosure(r, x, e)) r k
  | Variable x ->     continue !(try List.assoc x r with Not_found -> (Printf.printf "unset variable: %s\n" x; raise Not_found)) r k
  | If(e, e1, e2) ->  eval e r (IfCmd(e1, e2) :: k)
  | Cons(e1, e2) ->   eval e1 r (ConsCmd1 e2 :: k)
  | Car e ->          eval e r (CarCmd :: k)
  | Cdr e ->          eval e r (CdrCmd :: k)
  | SetCar(e1, e2) -> eval e1 r (SetCarCmd1 e2 :: k)
  | SetCdr(e1, e2) -> eval e1 r (SetCdrCmd1 e2 :: k)
  | Apply(f, args) -> eval f r (ApplyCmd1 args :: k)
  | Set(x, e) ->      eval e r (SetCmd x :: k)
  | LetCC(x, e) ->    eval e ((x, ref (ContClosure(r, k))) :: r) k
  | Throw(e1, e2) ->  eval e1 r (ThrowCmd1 e2 :: k)
and continue v r k =
  match v, k with
  | v, [] ->                                            v

  | car, ConsCmd1 cdr :: k ->                           eval cdr r (ConsCmd2 car :: k)
  | cdr, ConsCmd2 car :: k ->                           continue (ConsCell(ref car, ref cdr)) r k

  | v, SetCarCmd1 e :: k ->                             eval e r (SetCarCmd2 v :: k)
  | v, SetCarCmd2 ConsCell(r1, r2) :: k ->              r1 := v; continue NilV r k
  | v, SetCarCmd2 _ :: k ->                             failwith "setcar expected a cons cell"

  | v, SetCdrCmd1 e :: k ->                             eval e r (SetCdrCmd2 v :: k)
  | v, SetCdrCmd2 ConsCell(r1, r2) :: k ->              r2 := v; continue NilV r k
  | v, SetCdrCmd2 _ :: k ->                             failwith "setcdr expected a cons cell"

  | v, ThrowCmd1 e :: k ->                              eval e r (ThrowCmd2 v :: k)
  | ContClosure(r, k), ThrowCmd2 v :: _ ->              continue v r k
  | _, ThrowCmd2 v :: _ ->                              failwith "throw: expected a continuation"

  | ConsCell(car, cdr), CarCmd :: k ->                  continue !car r k
  | _, CarCmd :: k ->                                   failwith "car: expected a cons cell"

  | ConsCell(car, cdr), CdrCmd :: k ->                  continue !cdr r k
  | _, CdrCmd :: k ->                                   failwith "cdr: expected a cons cell"

  | f, ApplyCmd1(arg :: rest) :: k ->                   eval arg r (ApplyCmd2(f, [], rest) :: k)
  | FuncClosure(r, [], e), ApplyCmd1 [] :: k ->         eval e r k
  | _, ApplyCmd1 [] :: k ->                             failwith "apply: expected a function"

  | v, ApplyCmd2(f, vs, e :: es) :: k ->                eval e r (ApplyCmd2(f, (ref v) :: vs, es) :: k)
  | FuncClosure(r, xs, e), ApplyCmd2(f, vs, []) :: k -> eval e ((List.combine xs (List.rev vs)) @ r) k
  | _, ApplyCmd2(f, vs, []) :: k ->                     failwith "apply: expected a function"

  | BooleanV b, IfCmd(e1, e2) :: k ->                   eval (if b then e1 else e2) r k
  | _, IfCmd(e1, e2) :: k ->                            failwith "if: expected a Boolean value"

  | v, SetCmd(x) :: k ->                                let x = 
							  try List.assoc x r
							  with Not_found -> failwith ("set: undefined variable: " ^ x) in
							x := v;
                                                        continue NilV r k
