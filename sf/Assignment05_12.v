Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  assert(H0: forall (P:Prop), False -> P).
  - intros. inversion H.
  - induction n, m.
    + intros. unfold beq_nat. apply H0. apply H. reflexivity.
    + unfold beq_nat. reflexivity.
    + intros. reflexivity.
    + intros. apply IHn. unfold not. unfold not in H. intros. apply H. rewrite H1. reflexivity.
Qed.
(** [] *)




