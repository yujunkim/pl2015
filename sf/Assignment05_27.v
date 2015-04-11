Require Export Assignment05_26.

(* problem #27: 10 points *)


Theorem even__ev: forall n : nat,
  even n -> ev n.
Proof.
  induction n.
  - intros. apply ev_0.
  - intros. pose proof even__ev_strong as X. specialize (X (S n)). simpl in X. inversion X. apply H1. apply H.
Qed.
(** [] *)


