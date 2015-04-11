Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  intros n m. generalize dependent n. induction m.
  - destruct n.
    + intros. apply le_n.
    + simpl. intros. inversion H.
  - intros. destruct n.
    + apply O_le_n.
    + apply n_le_m__Sn_le_Sm. apply IHm.
                 simpl in H. apply H.
Qed.

