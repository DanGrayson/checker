(** In this file we implement structural comparison of expressions, modulo alpha equivalence and source code positions. *)

open Typesystem

let uequal2 : (uExpr * uExpr) -> bool = function
    _ -> false
let tequal2 : (tExpr * tExpr) -> bool = function
    _ -> false
let oequal2 : (oExpr * oExpr) -> bool = function
    _ -> false



let uequal a b = uequal2 (a,b)
let tequal a b = tequal2 (a,b)
let oequal a b = oequal2 (a,b)
