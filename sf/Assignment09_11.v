Require Export Assignment09_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, advanced, optional (is_wp_formal)  *)
(** Prove formally using the definition of [hoare_triple] that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp.
  split.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold beval, assn_sub, update, assert_implies. simpl. intros. omega.

  intros P' ht st P'_holds. unfold hoare_triple in ht.
  remember (update st X (st Y + 1)) as st'.
  assert ((X ::= APlus (AId Y) (ANum 1)) / st || st') as E. subst st'. apply E_Ass. reflexivity.
  apply ht in E; try assumption. rewrite Heqst' in E. unfold update in E. simpl in E.  omega.
Qed.

(*-- Check --*)
Check is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).

