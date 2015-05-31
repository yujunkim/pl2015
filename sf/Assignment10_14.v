Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint:

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to:
     Hint Constructors aval
     Hint Constructors astep.

   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  intros. induction a. left. eauto. right. eauto. right.

  inversion IHa1. inversion H. rewrite H0.
  inversion IHa2. inversion H1. rewrite H2. exists (ANum (x + x0)). eauto. inversion H1. inversion H2; eauto.

  inversion H. inversion H0; eauto.
  right.

  inversion IHa1. inversion H. rewrite H0.
  inversion IHa2. inversion H1. rewrite H2. exists (ANum (x - x0)). eauto. inversion H1. inversion H2; eauto.

  inversion H. inversion H0; eauto.

  right.
  inversion IHa1. inversion H. rewrite H0.
  inversion IHa2. inversion H1. rewrite H2. exists (ANum (x * x0)). eauto. inversion H1. inversion H2; eauto.

  inversion H. inversion H0; eauto.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

