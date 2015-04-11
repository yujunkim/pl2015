Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  assert(H8: forall m, beq_nat m m = true).
  - induction m. reflexivity. simpl. apply IHm.
  - induction n, m.
    + unfold beq_nat. intros. inversion H.
    + intros. unfold not. unfold beq_nat in H. intros. inversion H0.
    + intros. unfold beq_nat in H. intro H0. inversion H0.
    + intros. unfold not. intros. rewrite H0 in H. simpl in H. rewrite H8 in H. inversion H.
Qed.
(** [] *)



