Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint:

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.

   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros.
  induction c.
  left. reflexivity.
  right; induction a; eauto; inversion IHa1; inversion IHa2; inversion H; inversion H0; inversion H1; inversion H2; eauto.
  right.

  inversion IHc1. inversion IHc2. rewrite H. rewrite H0. eauto.
  rewrite H. inversion H0. inversion H1. eauto.

  inversion H. inversion H0. eauto.

  right.
  remember bexp_strong_progress.
  inversion IHc1. inversion IHc2. rewrite H. rewrite H0.
  generalize (o st b). intros. inversion H1. inversion H2. inversion H3. eauto. inversion H3. eauto. inversion H2. eauto.

  generalize (o st b). intros. inversion H1. inversion H2. inversion H3. eauto. inversion H3. eauto. inversion H2. eauto.

  generalize (o st b). intros. inversion H0. inversion H1. inversion H2. eauto. inversion H2. eauto. inversion H1. eauto.

  right.

  inversion IHc. rewrite H. eauto.
  inversion H. inversion H0. eauto.

  right.
  inversion IHc1. inversion IHc2. rewrite H. rewrite H0. eauto.
  rewrite H. inversion H0. inversion H1. eauto.
  inversion H. inversion H0. eauto.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/
  exists c' st', c / st ==>c c' / st'.

