Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. intros. induction c; simpl. apply refl_cequiv.
  - unfold cequiv. intros. split. intros.
    inversion H; subst. apply E_Ass. rewrite <- optimize_0plus_aexp_sound. reflexivity.
    intros. inversion H; subst. apply E_Ass. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - unfold cequiv. intros. split.
    intros. inversion H; subst. apply E_Seq with st'0.
      apply IHc1. apply H2.
      apply IHc2. apply H5.
    intros. inversion H; subst. apply E_Seq with st'0.
      apply IHc1. apply H2.
      apply IHc2. apply H5.
  - unfold cequiv. intros. split.
    intros. inversion H; subst.
      apply E_IfTrue. rewrite <- optimize_0plus_bexp_sound. apply H5. apply IHc1. apply H6.
      apply E_IfFalse. rewrite <- optimize_0plus_bexp_sound. apply H5. apply IHc2. apply H6.
    intros. inversion H; subst.
      apply E_IfTrue. rewrite <- optimize_0plus_bexp_sound in H5. apply H5. apply IHc1. apply H6.
      apply E_IfFalse. rewrite <- optimize_0plus_bexp_sound in H5. apply H5. apply IHc2. apply H6.
  - apply CWhile_congruence. apply optimize_0plus_bexp_sound. apply IHc.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

