Require Export Assignment08_10.

(* problem #11: 10 points *)

Theorem update_same : forall n1 x1 x2 (st : state),
  st x1 = n1 ->
  (update st x1 n1) x2 = st x2.
Proof.
  intros. unfold update. destruct (eq_id_dec x1 x2). rewrite <- e. rewrite H. reflexivity.
  reflexivity.
Qed.

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).
Proof.
  intros. intros st st'. split; intros. inversion H0; subst. assert(HH: st' = (update st' X (st' X))). apply functional_extensionality. intros. rewrite update_same. reflexivity. reflexivity. rewrite HH at 2. constructor. unfold aequiv in H. rewrite <- H. simpl. reflexivity. inversion H0. subst. replace (update st X (aeval st e)) with st. constructor. unfold aequiv in H. rewrite <- H. simpl. apply functional_extensionality. intros. rewrite update_same. reflexivity. reflexivity.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e ->
  cequiv SKIP (X ::= e).

