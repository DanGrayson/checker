Section A.
  (* 

  Kinds:
        Type
        Texp -> Type
        Oexp -> Texp -> Type
        Texp -> Texp -> Type
        Oexp -> Oexp -> Texp -> Type

  Type families: 
        Ulevel
        Texp
        Oexp
        Istype
        Hastype
        Teq
        Oeq
        Texp -> (Oexp -> Oexp) -> Oexp
        Oexp -> Oexp -> (Oexp -> Texp) -> Oexp
        Texp -> (Oexp -> Texp) -> Texp

  Terms:
        lamb
        ev
        empty_r
        For_all
        hastype_ev

  The relationship between these is described in the signature, which assigns
  type families to the constant terms and kinds to the constant type families,
  as we do in the axioms below.

  Theorem A below expresses a typing judgment for a term of TS.  The derivation
  of the judgment is a term A of LF of the given type, and is constructed using
  eta-reduction for the empty type.

    Theorem A:
      forall {T1 T2 T3 : Texp} {f o bad : Oexp},
        Istype T1 ->
        Istype T2 ->
        Hastype o T1 ->
        Hastype f (Arrow T2 T3) ->
        Hastype bad Empty ->
        Hastype (ev f o (fun _ => T3)) T3.

 *)

Axiom Texp Oexp : Type.
Axiom lamb : Texp -> (Oexp -> Oexp) -> Oexp.
Axiom ev : Oexp -> Oexp -> (Oexp -> Texp) -> Oexp.
Axiom empty_r : Texp -> Oexp -> Oexp.
Axiom For_all : Texp -> (Oexp -> Texp) -> Texp.

Definition Arrow (T U : Texp) := For_all T (fun _ => U).

Axiom Empty : Texp.

Axiom Istype : Texp -> Type.
Axiom Hastype : Oexp -> Texp -> Type.

Axiom hastype_ev :
  forall {T : Texp} {U : Oexp -> Texp} (g : Oexp) (x : Oexp),
    (Hastype x T) -> 
    (Hastype g (For_all T U)) ->
    Hastype (ev g x U) (U x).

Axiom Teq : Texp -> Texp -> Type.
Axiom Oeq : Oexp -> Oexp -> Texp -> Type.

Axiom hastype_lamb : 
  forall {T : Texp} {U : Oexp -> Texp} {f : Oexp -> Oexp},
    (forall x:Oexp, Hastype x T -> Hastype (f x) (U x)) 
    -> Hastype (lamb T f) (For_all T U).


Axiom istype_Empty : Istype Empty.
Axiom istype_Forall : 
  forall {T : Texp} {U : Oexp -> Texp},
    (forall x:Oexp, Hastype x T -> Istype (U x))
    -> Istype (For_all T U).
Axiom hastype_empty_r:
  forall {T : Texp} {o : Oexp},
    (Istype T) ->
    (Hastype o Empty) ->
    (Hastype (empty_r T o) T).
Axiom hastype_eq:
  forall {T U : Texp} {o: Oexp},
    (Teq T U) -> (Hastype o T) -> Hastype o U.
Axiom o_eq_beta:                (* rule 27 *)
  forall {T1 : Texp} {o1 : Oexp} {T2 : Oexp -> Texp} {o2 : Oexp -> Oexp},
    (Hastype o1 T1) ->
    (forall x:Oexp, Hastype (o2 x) (T2 x)) ->
    (Hastype (ev (lamb T1 o2) o1 T2) (T2 o1)).
Axiom teq_empty_eta:
  forall {T T' : Texp} {a : Oexp},
    (Hastype a Empty) -> 
    (Istype T) ->
    (Istype T') ->
    Teq T T'.
Theorem A:
  forall {T1 T2 T3 : Texp} {f o bad : Oexp},
    Istype T1 ->
    Istype T2 ->
    Hastype o T1 ->
    Hastype f (Arrow T2 T3) ->
    Hastype bad Empty ->
    Hastype (ev f o (fun _ => T3)) T3.
Proof.          
  intros * dT1 dT2 dO dF dBad.
  exact (hastype_ev _ _ (hastype_eq (teq_empty_eta dBad dT1 dT2) dO) dF).
  Defined.

Check @A.

(*

    m \in Fu

    Show that the following is a well form  sentence:

    x1: [U](m) , x2 : [El](x1)-> [U](m) , x3: [El](x1), x4 : [El] ( x2 x3) |- x3 : [El](x1) 

*)

Axiom Ulevel : Type.
Axiom UU : Ulevel -> Texp.      (* use UU for [U] *)
Axiom Rule15: forall (m : Ulevel), Istype (UU m).
Axiom El : Oexp -> Texp.
Axiom Rule17: forall (o: Oexp) (m: Ulevel), Hastype o (UU m) -> Istype (El o).
Axiom m : Ulevel.
Lemma i1 : Istype ( UU m ). 
  exact (Rule15 m).
Defined.
Axiom x1 : Oexp.
Axiom j1 : Hastype x1 ( UU m ).
Lemma arrowtype: forall (X Y : Texp), (Istype X) -> (Istype Y) -> (Istype (Arrow X Y)).
Proof.
  intros.
  apply (@istype_Forall _ (fun _ : Oexp => Y)).
  intros.  
  trivial.
Defined.

Lemma i2 : Istype ( Arrow (El x1) (UU m) ).
Proof.
  assert( i : Istype (El x1) ).
    apply (Rule17 _ m).
    apply j1.
  assert( j : Istype (UU m) ).
    apply Rule15.
  apply arrowtype.
  trivial.  
  trivial.
Defined.

Axiom x2 : Oexp.
Axiom j2 : Hastype x2 ( Arrow (El x1) (UU m) ).

Lemma i3 : Istype (El x1).
Proof.
  apply (Rule17 _ m).
  apply j1.
Defined.

Axiom x3 : Oexp.
Axiom j3 : Hastype x3 (El x1).

Lemma i4 : Istype (El (ev x2 x3 (fun _ : Oexp => UU m))).
Proof.
  apply (Rule17 _ m).
  apply (@hastype_ev _ (fun _ : Oexp => UU m) _ _ j3 j2).
Defined.

Axiom x4 : Oexp.
Axiom j4 : Hastype x4 (El (ev x2 x3 (fun _ : Oexp => UU m))).

Theorem B : Hastype x3 (El x1).
Proof.
  apply j3.
Defined.
