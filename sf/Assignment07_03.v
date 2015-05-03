Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq : forall (e1 e2: aexp) (n1 n2 : nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      bevalR (BEq e1 e2) (beq_nat n1 n2)
  | E_BLe : forall (e1 e2: aexp) (n1 n2 : nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      bevalR (BLe e1 e2) (ble_nat n1 n2)
  | E_BNot : forall (e1: bexp) (b1 : bool),
      bevalR e1 b1 ->
      bevalR (BNot e1) (negb b1)
  | E_BAnd : forall (e1 e2: bexp) (b1 b2 : bool),
      bevalR e1 b1 ->
      bevalR e2 b2 ->
      bevalR (BAnd e1 e2) (andb b1 b2).

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  intros.
  split.
  intros.
  induction H ; simpl.
    try(simpl; reflexivity).
    try(simpl; reflexivity).
    try(apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; rewrite H; rewrite H0; reflexivity).
    try(apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; rewrite H; rewrite H0; reflexivity).
    try(rewrite IHbevalR; reflexivity).
    try(rewrite IHbevalR1; rewrite IHbevalR2; reflexivity).
  intros.
  generalize dependent bv.
  induction b; simpl ; intros; rewrite <- H.
    try (apply E_BTrue).
    try (apply E_BFalse).
    try (apply E_BEq; apply aeval_iff_aevalR; reflexivity).
    try (apply E_BLe; apply aeval_iff_aevalR; reflexivity).
    try (apply E_BNot; apply IHb; reflexivity).
    apply E_BAnd. apply IHb1. reflexivity. apply IHb2. reflexivity.
Qed.

(** [] *)

