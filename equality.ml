(** In this file, we implement definitional equality.

    In phase 1, it's the same as alpha-equivalence. *)

open Typesystem

let uequal = Alpha.uequal
let tequal = Alpha.tequal
let oequal = Alpha.oequal
