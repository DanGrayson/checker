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

let fixParmList (p:parm list) : uContext * (var' list) * ((var' * ts_expr) list) = (* this code has to be moved somewhere to use the context *)
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

let tDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var' list) * ((var' * ts_expr) list))) (t:ts_expr)
    : (string * int * Error.position * lf_expr * lf_type) list 
    = 
  let (pos,t0) = t in 
  let UContext (uvars,ueqns) = ulevel_context
  in let wt = ATOMIC t
  in let wk = texp

  in let wt = List.fold_right
      (fun (z,u) t -> LAMBDA(nowhere(newfresh z),t))
      ts_context wt

  in let wk = List.fold_right
      (fun (z,u) t -> nowhere (F_Pi(VarUnused,hastype (to_lfexpr' z) (ATOMIC u), t)))
      ts_context wk

  in let wt = List.fold_right
      (fun v t -> LAMBDA((nowhere v),t))
      (List.flatten [uvars; tc; (List.map fst ts_context)]) wt

  in let f sort = fun v t -> nowhere (F_Pi(v,sort,t))

  in let wk = List.fold_right (f oexp) (List.map fst ts_context) wk
  in let wk = List.fold_right (f texp) tc wk
  in let wk = List.fold_right (f uexp) uvars wk

  in
  [ 
    ( name, 0, pos, wt, wk );
    ( name, 1, pos, ATOMIC(new_hole()), istype (ATOMIC t))
  ]

let oDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var' list) * ((var' * ts_expr) list))) (o:ts_expr) (t:ts_expr)
    : (string * int * Error.position * lf_expr * lf_type) list 
    = 
  (* still have to wrap the lambdas around it : *)
  [
   ( name, 0, get_pos o, ATOMIC o, oexp);
   ( name, 1, get_pos t, ATOMIC t, texp);
   ( name, 2, get_pos o, ATOMIC (new_hole()), hastype (ATOMIC o) (ATOMIC t))
 ]

let teqDefinition _ _ _ _ = raise (Error.Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Error.Unimplemented "oeqDefinition")
