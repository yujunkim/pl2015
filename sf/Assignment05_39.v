Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m. generalize dependent n. induction m.
  - destruct n.
    + intros. unfold ble_nat in H. inversion H.
    + intros. unfold not. intros. inversion H0.
  - intros. destruct n.
    + unfold not. intros. unfold ble_nat in H. inversion H.
    + simpl in H. apply IHm in H. unfold not. unfold not in H. intros. apply Sn_le_Sm__n_le_m in H0. apply H in H0. inversion H0.
Qed.
(** [] *)

