Require Export Assignment05_14.

(* problem #15: 10 points *)



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  intros. induction n.
  - unfold double. apply ev_0.
  - unfold double. apply ev_SS. apply IHn.
Qed.
(** [] *)




