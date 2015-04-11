Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_n_O : forall n : nat,
  n = n + 0.
Proof.
  intros. symmetry. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_comm : forall n m,
  n + m = m + n.
Proof.
  intros. induction n.
  - simpl. symmetry. rewrite -> plus_n_O. reflexivity.
  - simpl. rewrite -> IHn. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros. split.
  - apply le_trans with (n := S (n1 + n2)). apply n_le_m__Sn_le_Sm. apply le_plus_l. apply H.
  - apply le_trans with (n := S (n1 + n2)). apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l. apply H.
Qed.

