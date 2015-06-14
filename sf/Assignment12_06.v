Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof with eauto.
  intros not. inversion not. inversion H.
  unfold normal_form in H1.

  apply H1.
  inversion H0. subst. subst. eapply ex_intro. unfold tloop. eauto.
  inversion H2. solve by inversion 3. solve by inversion. subst.
  inversion H3. eapply ex_intro. unfold tloop. eauto.
  inversion H4; try solve by inversion. subst.
  inversion H13; try solve by inversion.
  subst.
  inversion H5. simpl. eauto 12.
  inversion H6; try solve by inversion. subst.

  inversion H7. simpl. eauto 12.
  inversion H9. try solve by inversion 3.  try solve by inversion. subst.

  remember (tapp tloop (tnat 0)) as p.
  remember (tapp
       (tapp
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X))))
          (tfix
             (tabs Loop (TArrow TNat TNat)
                (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)) as q.
  remember (tapp
       ([Loop
        := tfix
             (tabs Loop (TArrow TNat TNat)
                (tabs X TNat (tapp (tvar Loop) (tvar X))))]
        tabs X TNat (tapp (tvar Loop) (tvar X))) (tnat 0)) as r.

  remember ([X := tnat 0]
     tapp
       (tfix
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X))))) (tvar X)) as s.
  assert (x = p \/ x = q \/ x = r \/ x = s).
  admit.

  inversion H12. rewrite H15. eauto.
  inversion H15. rewrite H16. eauto.
  inversion H16. rewrite H17. eauto. rewrite H17. eauto.

  try solve by inversion 3.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

Require Export Assignment12_05.

(* problem #06: 10 points *)

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof with eauto.
  intros not. inversion not. inversion H.
