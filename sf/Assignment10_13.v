Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros. inversion H. induction n.
  exists st. split. apply multi_refl. apply H.
  inversion IHn.
  exists (update x X (S n)).
  split.
  eapply multi_trans.
  apply H2.
  apply par_body_n__Sn.
  apply H2.
  split.
  apply update_eq.
  inversion H2.
  inversion H4.
  rewrite <- H6.
  simpl.
  unfold update. simpl. reflexivity.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

