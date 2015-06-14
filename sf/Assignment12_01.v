Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  intros not.
  inversion not. inversion H.
  inversion H0; subst; clear H0.
  inversion H6; subst; clear H6.
  inversion H5; subst; clear H5.
  inversion H3; subst; clear H3.
  inversion H2.
  subst.
  induction T1; try inversion H4.
  apply IHT1_1. eapply ex_intro. apply T_Abs.
  eapply T_App. apply T_Var. rewrite H1. unfold extend. simpl. eauto. auto. auto. rewrite H1.  auto.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |-
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

