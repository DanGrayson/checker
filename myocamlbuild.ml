open Ocamlbuild_plugin;;

let common_flags = [ A "-g"; A "-annot"; A "-w"; A "@8"; A "-I"; A "+camlp5" ]
let native_flags = common_flags @ [A "-S"; A "pa_macro.cmx"]
let byte_flags   = common_flags @ [        A "pa_macro.cmo"]

;;flag ["ocaml"; "compile"; "byte"  ] (S byte_flags)
;;flag ["ocaml"; "compile"; "native"] (S native_flags)

 (* @8 above refers to Warning 8: this pattern-matching is not exhaustive. *)
