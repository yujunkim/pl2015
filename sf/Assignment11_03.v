Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
   unfold deterministic. intros x y1 y2 st1. generalize dependent y2.
  step_cases (induction st1) Case; intros y2 st2.
    Case "ST_IfTrue". inversion st2; try solve by inversion. reflexivity.
    Case "ST_IfFalse". inversion st2; try solve by inversion. reflexivity.
    Case "ST_If". inversion st2; subst; try solve by inversion.
      rewrite (IHst1 t1'0 H3). reflexivity.
    Case "ST_Succ". inversion st2; subst. rewrite (IHst1 t1'0 H0). reflexivity.
    Case "ST_PredZero". inversion st2; try solve by inversion. reflexivity.
    Case "ST_PredSucc". inversion st2; subst.
      reflexivity.
      inversion H1; subst.
        assert (step_normal_form t1) as snf_t1. apply value_is_nf. auto.
        exfalso. apply snf_t1. exists t1'0. apply H2.
    Case "ST_Pred". inversion st2; subst; try solve by inversion.
      inversion st1; subst.
        assert (step_normal_form y2) as snf_y2. apply value_is_nf. auto.
        exfalso. apply snf_y2. exists t1'0. apply H1.
      rewrite (IHst1 t1'0 H0). reflexivity.
    Case "ST_IszeroZero". inversion st2; try solve by inversion. reflexivity.
    Case "ST_IszeroSucc". inversion st2.
      reflexivity.
      inversion H1; subst.
        assert (step_normal_form t1) as snf_t1. apply value_is_nf. auto.
        exfalso. apply snf_t1. exists t1'0. apply H4.
    Case "ST_Iszero". inversion st2; subst; try solve by inversion.
      inversion st1; subst.
        assert (step_normal_form t0) as snf_t0. apply value_is_nf. auto.
        exfalso. apply snf_t0. exists t1'0. apply H1.
      rewrite (IHst1 t1'0 H0). reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

