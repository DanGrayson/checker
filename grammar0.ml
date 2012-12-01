(** Parsing: auxiliary functions. *)

open Typesystem
open Helpers

let emptyUContext = UContext ([],[])
let mergeUContext : uContext -> uContext -> uContext =
  function UContext(uvars,eqns) -> function UContext(uvars',eqns') -> UContext(List.rev_append uvars' uvars,List.rev_append eqns' eqns)

type parm =
  | UParm of uContext
  | TParm of var' list
  | OParm of (var' * ts_expr) list

let fixParmList (p:parm list) : uContext * (var' list) * ((var' * ts_expr) list) =
  let rec fix us ts os p =
    match p with 
    | UParm u :: p -> 
	if List.length ts > 0 or List.length os > 0 then raise (Error.GeneralError "expected universe-level variables first");
	fix (u::us) ts os p
    | TParm t :: p -> 
	if List.length os > 0 then raise (Error.Unimplemented "a type parameter after an object parameter");
	fix us (t::ts) os p
    | OParm o :: p -> fix us ts (o::os) p
    | [] -> ( 
	let tc = List.flatten (List.rev_append ts [])
	and ts_context = List.flatten (List.rev_append os [])
	and ulevel_context = match (List.rev_append us []) with
	| [] -> emptyUContext
	| (ulevel_context :: []) -> ulevel_context
	| _ -> raise (Error.Unimplemented "merging of universe level variable lists")
	in (ulevel_context,tc,ts_context))
  in fix [] [] [] p

let tDefinition (name:string) ((ulevel_context,tvars,ts_context):(uContext * (var' list) * ((var' * ts_expr) list))) (t:ts_expr)
    : (var' * Error.position * lf_expr * lf_type) list 
    = 
  let pos = get_pos t in

  let v0 = VarDefined(name,0) in
  let v1 = VarDefined(name,1) in

  let tm = ATOMIC t in
  let tp = texp in
  let UContext (uvars,ueqns) = ulevel_context in
  let ovars = List.map fst ts_context in
  let hastvars = List.map (fun (z,u) -> newfresh z) ts_context in

  let tm = List.fold_right
      (fun v t -> LAMBDA(nowhere v,t))
      hastvars tm in
  let tp = List.fold_right
      (fun (z,u) t -> nowhere (F_Pi(VarUnused,hastype (to_lfexpr' z) (ATOMIC u), t)))
      ts_context tp in

  let g v t = LAMBDA((nowhere v),t) in
  let h sort v t = nowhere (F_Pi(v,sort,t)) in

  let tm = List.fold_right g ovars tm in
  let tp = List.fold_right (h oexp) ovars tp in

  let tm = List.fold_right g tvars tm in
  let tp = List.fold_right (h texp) tvars tp in

  let tm = List.fold_right g uvars tm in
  let tp = List.fold_right (h uexp) uvars tp in

  [ 
    ( v0, pos, tm, tp );
    ( v1, pos, ATOMIC(new_hole()), istype (ATOMIC t))
  ]

let oDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var' list) * ((var' * ts_expr) list))) (o:ts_expr) (t:ts_expr)
    : (var' * Error.position * lf_expr * lf_type) list 
    = 
  (* still have to wrap the lambdas around it : *)
  [
   ( VarDefined(name, 0), get_pos o, ATOMIC o, oexp);
   ( VarDefined(name, 1), get_pos t, ATOMIC t, texp);
   ( VarDefined(name, 2), get_pos o, ATOMIC (new_hole()), hastype (ATOMIC o) (ATOMIC t))
 ]

let teqDefinition _ _ _ _ = raise (Error.Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Error.Unimplemented "oeqDefinition")
