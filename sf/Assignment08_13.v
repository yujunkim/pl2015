Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  intros. intros st st'. split. intros. inversion H2; subst.
  apply E_IfTrue. unfold bequiv in H. rewrite <- H. apply H8. apply H0. apply H9.
  apply E_IfFalse. unfold bequiv in H. rewrite <- H. apply H8. apply H1. apply H9.
  intros. inversion H2; subst.
  apply E_IfTrue. unfold bequiv in H. rewrite H. apply H8. apply H0. apply H9.
  apply E_IfFalse. unfold bequiv in H. rewrite H. apply H8. apply H1. apply H9.
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

