Require Export Assignment10_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (multistep_congr_2)  *)
Lemma multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.
Proof.
  intros.
  inversion H.
  induction H0. apply multi_refl.
  subst. apply multi_step with (P (C n) y). apply ST_Plus2. apply H. apply H0. apply IHmulti.
Qed.

(*-- Check --*)
Check multistep_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     P t1 t2 ==>* P t1 t2'.

