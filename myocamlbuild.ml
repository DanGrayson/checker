open Ocamlbuild_plugin;;

(* see comments in ocaml-4.00.0/ocamlbuild/signatures.mli for some documentation *)

(*
  I don't know how to give these options to ocamlbuild here:
  "-menhir"; "menhir --explain";
  "-use-menhir";
*)

let cflags = [ "-g"; 
	       "-annot"; 
	       "-w"; 
	       "@8"       (* @8 refers to Warning 8: this pattern-matching is not exhaustive. *)
	     ]
let lflags = [ "-g" ]

let atomize args = List.map (fun arg -> A arg) args
let flag' flags args = flag flags (S (atomize args))

let _ =
  flag' ["ocaml"; "compile"; "native"] (cflags @ [ "-S" (* ;"pa_macro.cmx" *) ]);
  flag' ["ocaml"; "compile"; "byte"  ] (cflags @ [      (*  "pa_macro.cmo" *) ]);
  flag' ["ocaml"; "link"             ] (lflags @ [ "-g" ]);
  flag' ["ocaml"; "yacc"             ] [ "-v" ];


