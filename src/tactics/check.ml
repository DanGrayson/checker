open Helpers
open Typesystem
open Lfcheck
open Printer
open Printf

(** print the arguments and their types *)
let check surr env pos t args =
  args_iter 
    (fun x -> printf "$check = %a\n       : %a\n%!" _e x _t (un_singleton (snd (type_synthesis env x))))
    (fun () -> ())
    (fun () -> ())
    args;
  TacticFailure

(* 
  Local Variables:
  compile-command: "make -C ../.. src/tactics/check.cmo "
  End:
 *)
