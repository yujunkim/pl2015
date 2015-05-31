Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint:

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:.
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  remember aexp_strong_progress.
  intros. induction b. eauto. eauto.
  right. generalize (o st a). generalize (o st a0). intros.

  inversion H; inversion H0; inversion H1; inversion H2; inversion H3; inversion H4; eauto.

  right. generalize (o st a). generalize (o st a0). intros.
  inversion H; inversion H0; inversion H1; inversion H2; inversion H3; inversion H4; eauto.

  right. inversion IHb. inversion H. inversion H0. eauto. inversion H0. eauto. inversion H. eauto.
  right. inversion IHb1; inversion IHb2; inversion H; inversion H0; inversion H1; inversion H2; eauto.

Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

