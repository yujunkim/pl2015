Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros. split.
  - intros. destruct H.
    + split. apply or_introl. apply H. apply or_introl. apply H.
    + destruct H. split. apply or_intror. apply H. apply or_intror. apply H0.
  - intros. destruct H. destruct H,H0.
    + apply or_introl. apply H.
    + apply or_introl. apply H.
    + apply or_introl. apply H0.
    + apply or_intror. split. apply H. apply H0.
Qed.
(** [] *)


