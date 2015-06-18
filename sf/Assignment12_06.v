Require Export Assignment12_05.

(* problem #06: 10 points *)
Theorem MoreStlc_value_is_nf: forall v t,
  value v -> v ==> t -> False.
Proof with eauto.
  intros; generalize dependent t; assert (normal_form step v)...
  unfold normal_form; intros; induction H; intros contra; destruct contra;
  try solve by inversion; try inversion H0; try inversion H1; subst...
Qed.

Hint Resolve MoreStlc_value_is_nf.

Theorem MoreStlc_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic; intros; generalize dependent y2;
  induction H as [| |? ? ? ? P| | | | | |? ? ? ? P| | | | | |? ? ? ? P| |? ? ? P|
  |? ? ? P| | | | | | | | |? ? ? ? P| | | ? ? ? ? ? ? P| |? ? ? P]; intros;
  inversion H0; subst; try solve by inversion;
  try replace t0'0 with t0';
  try replace t1'0 with t1';
  try replace t2'0 with t2';
  eauto; exfalso...
Qed.
Hint Resolve MoreStlc_deterministic.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof with eauto.
  unfold tloop.
  intros not. inversion not. inversion H.
  unfold normal_form in H1.


  apply H1.
  inversion H0. subst. subst. eapply ex_intro. unfold tloop. eauto.
  inversion H2. solve by inversion 3. solve by inversion. subst.
  inversion H3. eapply ex_intro. unfold tloop. eauto.
  inversion H4; try solve by inversion. subst.
  inversion H13; try solve by inversion.
  subst.
  simpl in H5.
  simpl in H4.
  inversion H5. simpl. eauto 12.
  inversion H6; try solve by inversion. subst.
  simpl in H6.
  simpl in H7.

  remember (tapp
      (tfix
         (tabs Loop (TArrow TNat TNat)
            (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tnat 0)) as p.
  remember (tapp
       (tapp
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X))))
          (tfix
             (tabs Loop (TArrow TNat TNat)
                (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)) as q.
  remember (tapp
       (tabs X TNat
          (tapp
             (tfix
                (tabs Loop (TArrow TNat TNat)
                   (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tvar X)))
       (tnat 0)) as r.
  assert (forall t k, t = p \/ t = q \/ t = r ->
    t ==>* k -> k = p \/ k = q\/ k = r).
  {
    intros.
    induction H11. eauto. apply IHmulti. inversion H9. rewrite H15 in H11. eauto.
    inversion H15. rewrite H16 in H11. eauto. rewrite H16 in H11. eauto.
  }
  assert (x = p \/ x = q \/ x = r).
  apply H9 with (t:=p).
  eauto. eauto.
  inversion H11. subst x. eauto. inversion H12. subst x. eauto. subst x. eauto.
  try solve by inversion 3.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

