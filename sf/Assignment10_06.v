Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
    Case "C". left. apply v_const.
    Case "P". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (C (n + n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (P t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0].
          exists (P t' t2).
          apply ST_Plus1. apply H0.  Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.

  multi_cases (induction P11) Case.
  Case "multi_refl".
    intros.
    inversion P21.
    reflexivity.
    apply nf_is_value in P12.
    inversion P12.
    subst.
    inversion H.
  Case "multi_step".
    intros.
    apply IHP11; try assumption.
    multi_cases (inversion P21) SCase; subst.
    apply nf_is_value in P22.
    inversion P22.
    subst.
    inversion H.

    assert (deterministic step).
    apply step_deterministic_alt.
    unfold deterministic in H2.
    assert (y = y0).
    apply H2 with x.
    assumption.
    assumption.
    rewrite H3.
    assumption.
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

