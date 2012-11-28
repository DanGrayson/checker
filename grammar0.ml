(** Parsing: auxiliary functions. *)

open Typesystem
open Helpers

type parm =
  | UParm of uContext
  | TParm of var' list
  | OParm of (var' * expr) list

let fixParmList (p:parm list) : uContext * (var' list) * ((var' * expr) list) = (* this code has to be moved somewhere to use the context *)
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

let tDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var' list) * ((var' * expr) list))) (t:expr) : (string * int * expr * lftype) list = 
  let UContext (uvars,ueqns) = ulevel_context in
  let rec wrap t = function
    | [] -> t 
    | v :: rest -> wrap (LAMBDA((Error.Nowhere,v),t)) rest
  in let rec wrapk tf t = function
    | [] -> t 
    | v :: rest -> wrapk tf (F_Pi(v,tf,t)) rest
  in let rec wrapi t = function
    | [] -> t
    | (z,u) :: rest -> 
	let t = F_Pi(VarUnused,hastype (nowhere (Variable z)) u,t) in
	let t = F_Pi(VarUnused,istype u,t) in
	wrapi t rest
  in let k = texp
  in let wt = t
  in let wt = wrap wt (List.rev_append (List.map fst ts_context) [])
  in let wt = wrap wt (List.rev_append tc [])
  in let wt = wrap wt (List.rev_append uvars [])
  in let wk = k
  in let wk = wrapi wk (List.rev_append ts_context [])
  in let wk = wrapk oexp wk (List.rev_append (List.map fst ts_context) [])
  in let wk = wrapk texp wk (List.rev_append tc [])
  in let wk = wrapk uexp wk (List.rev_append uvars [])
  in
  [ 
    ( name, 0, wt, wk );
    ( name, 1, new_hole(), istype t)
  ]

let oDefinition (name:string) ((ulevel_context,tc,ts_context):(uContext * (var' list) * ((var' * expr) list))) (o:expr) (t:expr) : (string * int * expr * lftype) list = 
  (* still have to wrap the lambdas around it : *)
  [
   ( name, 0, o, oexp);
   ( name, 1, t, texp);
   ( name, 2, new_hole(), hastype o t)
 ]

let teqDefinition _ _ _ _ = raise (Error.Unimplemented "teqDefinition")

let oeqDefinition _ _ _ _ _ = raise (Error.Unimplemented "oeqDefinition")
