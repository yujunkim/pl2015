Require Export Assignment05_10.

(* problem #11: 10 points *)


(** 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).
Proof.
  intro P. intro H0. apply H0. apply or_intror. intro H. apply H0. apply or_introl. apply H.
Qed.




