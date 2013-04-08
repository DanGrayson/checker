(** Contexts. *)

open Judgments
open Relative
open Error

module MapString = Map.Make(String)
module MapIdentifier = Map.Make(Identifier)

type environment = {
    state : int;
    local_tts_context : (string * tts_declaration) list;
    global_tts_context : tts_declaration MapString.t;
    local_lf_context : (identifier * judgment) list;
    global_lf_context : judgment MapIdentifier.t;
  }

(** Functions *)

let empty_environment = {
  state = 0;
  local_tts_context = [];
  global_tts_context = MapString.empty;
  local_lf_context = [];
  global_lf_context = MapIdentifier.empty;
}

let interactive = ref false

let incr_state env =
  if !interactive
  then { env with state = env.state + 1 }
  else env

let local_lf_bind env v t = { env with local_lf_context = (v,t) :: env.local_lf_context }

let local_lf_fetch env i = 			(* (Rel i) *)
  try rel_shift_type (i+1) (snd (List.nth env.local_lf_context i))
  with Failure "nth" -> raise Not_found

let global_lf_bind env pos name t = 
  if MapIdentifier.mem name env.global_lf_context then raise (MarkedError (pos, "identifier already defined: " ^ idtostring name));
  { env with global_lf_context = MapIdentifier.add name t env.global_lf_context }

let global_lf_fetch env name = MapIdentifier.find name env.global_lf_context

let lf_fetch env = function
  | Var name -> global_lf_fetch env name
  | Rel i -> local_lf_fetch env i

let local_tts_declare_type   env name   = { env with local_tts_context = (name,(TTS_istype, None)) :: env.local_tts_context }

let local_tts_declare_object env name t = { env with local_tts_context = (name,(TTS_hastype t, None)) :: env.local_tts_context }

let global_tts_declare_type env pos name = 
  if MapString.mem name env.global_tts_context then raise (MarkedError (pos, "variable already defined: " ^ name));
  { env with global_tts_context = MapString.add name (TTS_istype, None) env.global_tts_context }

let global_tts_declare_object env pos name t = 
  if MapString.mem name env.global_tts_context then raise (MarkedError (pos, "variable already defined: " ^ name));
  { env with global_tts_context = MapString.add name (TTS_hastype t, None) env.global_tts_context }

let ts_bind env v t = 
  if isid v then local_tts_declare_object env (id_to_name v) t else raise Internal

let local_tts_fetch env i =			(* (Rel i) *)
  match List.nth env.local_tts_context i with
  | (_, (TTS_istype, _)) -> TTS_istype
  | (_, (TTS_hastype t, _)) -> TTS_hastype (rel_shift_expr (i+1) t)
  | (_, (TTS_type_equality(t,t'),_)) -> raise NotImplemented
  | (_, (TTS_object_equality(t,o,o'),_)) -> raise NotImplemented
  | (_, (TTS_template _,_)) -> raise NotImplemented

let global_tts_fetch env name = fst (MapString.find name env.global_tts_context)

let global_tts_fetch_type env name =
  match global_tts_fetch env name with
  | TTS_hastype t -> t
  | TTS_istype 
  | TTS_type_equality _
  | TTS_object_equality _
  | TTS_template _
    -> raise Not_found

let is_tts_type_variable env name =
  try match global_tts_fetch env name with
  | TTS_istype -> true
  | TTS_hastype _
  | TTS_type_equality _
  | TTS_object_equality _
  | TTS_template _ -> false
  with
  | Not_found -> false

let tts_fetch env = function
  | Var id -> global_tts_fetch env (id_to_name id)
  | Rel i -> local_tts_fetch env i

let tts_fetch_type env name =
  match tts_fetch env name with
  | TTS_hastype t -> t
  | TTS_istype
  | TTS_type_equality _
  | TTS_object_equality _
  | TTS_template _
    -> raise Not_found

let ts_fetch env v = 
  match tts_fetch env v with
  | TTS_hastype t -> t
  | TTS_istype
  | TTS_type_equality _
  | TTS_object_equality _
  | TTS_template _
    -> raise Internal

let first_var env =
  match env.local_tts_context with
  | (name,_) :: _ -> id name
  | _ -> raise Internal

type uContext = UContext of var marked list * (expr * expr) marked list

let empty_uContext = UContext([],[])

(*
  Local Variables:
  compile-command: "make -C .. src/contexts.cmo "
  End:
 *)
