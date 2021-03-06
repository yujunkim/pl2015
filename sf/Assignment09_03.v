Require Export Assignment09_02.

(* problem #03: 10 points *)

(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  exists (APlus (AId X) (ANum 1)).
  simpl.
  intros not.
  unfold beval, assn_sub, update, hoare_triple, assert_implies in not.
  remember empty_state as st.
  remember (update st X (st X + 1)) as st'.
  assert ((X ::= (APlus (AId X) (ANum 1))) / st || st') as HH.

  rewrite Heqst. rewrite Heqst'. subst. apply E_Ass. reflexivity.

  subst. apply not in HH. inversion HH. auto.
Qed.

(*-- Check --*)
Check hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.

