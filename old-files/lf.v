Section A.
Axiom Texp Oexp : Type.
Axiom lamb : Texp -> (Oexp -> Oexp) -> Oexp.
Axiom ev : Oexp -> Oexp -> (Oexp -> Texp) -> Oexp.
Axiom empty_r : Texp -> Oexp -> Oexp.
Axiom Forall : Texp -> (Oexp -> Texp) -> Texp.

Definition Arrow (T U : Texp) := Forall T (fun _ => U).

Axiom Empty : Texp.

Axiom istype : Texp -> Type.
Axiom hastype : Oexp -> Texp -> Type.
Axiom teq : Texp -> Texp -> Type.
Axiom oeq : Oexp -> Oexp -> Texp -> Type.

Axiom istype_Empty : istype Empty.
Axiom istype_Forall : 
  forall {T : Texp} {U : Oexp -> Texp},
    (forall x:Oexp, hastype x T -> istype (U x))
    -> istype (Forall T U).
Axiom hastype_lamb : 
  forall {T : Texp} {U : Oexp -> Texp} {f : Oexp -> Oexp},
    (forall x:Oexp, hastype x T -> hastype (f x) (U x)) 
    -> hastype (lamb T f) (Forall T U).
Axiom hastype_ev :
  forall {T : Texp} {U : Oexp -> Texp} {g : Oexp} {x : Oexp},
    (hastype x T) -> 
    (hastype g (Forall T U)) ->
    hastype (ev g x U) (U x).
Axiom hastype_empty_r:
  forall {T : Texp} {o : Oexp},
    (istype T) ->
    (hastype o Empty) ->
    (hastype (empty_r T o) T).
Axiom hastype_eq:
  forall {T U : Texp} {o: Oexp},
    (teq T U) -> (hastype o T) -> hastype o U.
Axiom o_eq_beta:                (* rule 27 *)
  forall {T1 : Texp} {o1 : Oexp} {T2 : Oexp -> Texp} {o2 : Oexp -> Oexp},
    (hastype o1 T1) ->
    (forall x:Oexp, hastype (o2 x) (T2 x)) ->
    (hastype (ev (lamb T1 o2) o1 T2) (T2 o1)).
Axiom teq_empty_eta:
  forall {T T' : Texp} {a : Oexp},
    (hastype a Empty) -> 
    (istype T) ->
    (istype T') ->
    teq T T'.
Theorem A:
  forall {T1 T2 T3 : Texp} {f o bad : Oexp},
    istype T1 ->
    istype T2 ->
    hastype o T1 ->
    hastype f (Arrow T2 T3) ->
    hastype bad Empty ->
    hastype (ev f o (fun _ => T3)) T3.
Proof.          
  intros * dT1 dT2 dO dF dBad.
  exact (hastype_ev (hastype_eq (teq_empty_eta dBad dT1 dT2) dO) dF).
  Defined.

Check @A.
