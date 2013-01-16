(** apply an inference rule *)

open Error
open Typesystem
open Lfcheck
open Names
open Printer
open Printf

let rec apply surr env pos t args = 
  match args with
  | ARG(f,args) -> (
      let (f',t') = type_synthesis env f in
      let t' = un_singleton t' in (* type_synthesis returns the most specific type, but what if the type of f really is a singleton? *)
      printf "$apply should unify\n\t t  = %a\n\t t' = %a\n%!" _t t _t t';
      raise (TypeCheckingFailure (env, surr, [ pos, "$apply: not implemented yet" ] ))
     )
  | _ -> raise (TypeCheckingFailure (env, surr, [ pos, "$apply expected a function" ] ))

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/apply.cmo "
  End:
 *)
