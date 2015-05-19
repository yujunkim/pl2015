Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.
Proof.
  intros.
  intros st st'.
  split. intros. inversion H0. subst. unfold bequiv in H. rewrite H in H6. inversion H6. subst. apply H7.
  intros. apply E_IfFalse. unfold bequiv in H. rewrite H. simpl. reflexivity. apply H0.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv
    (IFB b THEN c1 ELSE c2 FI)
    c2.

