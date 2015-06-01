Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Check andb_prop.

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | ttrue =>
      match T with
      | TBool => true
      | TNat => false
      end
  | tfalse =>
      match T with
      | TBool => true
      | TNat => false
      end
  | tif b t1 t2 =>
      (tycheck b TBool) && (tycheck t2 T) && (tycheck t1 T)
  | tzero =>
      match T with
      | TBool => false
      | TNat => true
      end
  | tsucc t =>
      match T with
      | TBool => false
      | TNat => tycheck t T
      end
  | tpred t =>
      match T with
      | TBool => false
      | TNat => tycheck t T
      end
  | tiszero t =>
      match T with
      | TBool => tycheck t TNat
      | TNat => false
      end
  end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero)))
    TBool
  = true.
Proof. simpl. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero)))
    TBool
  = false.
Proof. simpl. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  induction t. intros. induction T. eauto. inversion TYCHK.

  induction T. intros. eauto. intros. inversion TYCHK.
  induction T. intros. inversion TYCHK.

  apply andb_prop in H0. inversion H0.
  apply andb_prop in H. inversion H.
  apply T_If.
  apply IHt1. apply H2.
  apply IHt2. apply H1.
  apply IHt3. apply H3.
  intros. inversion TYCHK.
  apply andb_prop in H0. inversion H0.
  apply andb_prop in H. inversion H.
  apply T_If.
  apply IHt1. apply H2.
  apply IHt2. apply H1.
  apply IHt3. apply H3.

  intros. inversion TYCHK. induction T. inversion H0. apply T_Zero.
  induction T. simpl. intros. inversion TYCHK.
  intros. simpl. apply T_Succ. apply IHt. simpl. simpl in TYCHK. apply TYCHK.

  induction T. simpl. intros. inversion TYCHK.
  intros. simpl. apply T_Pred. apply IHt. simpl. simpl in TYCHK. apply TYCHK.

  intros. induction T. apply T_Iszero. simpl in TYCHK. apply IHt. apply TYCHK.
  inversion TYCHK.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  induction t.
  intros. induction T. eauto. inversion HASTY.
  intros. induction T. eauto. inversion HASTY.
  intros. induction T. simpl. unfold andb. rewrite IHt1. rewrite IHt3. rewrite IHt2. reflexivity. inversion HASTY; assumption. inversion HASTY; assumption. inversion HASTY; assumption.
  simpl. unfold andb. rewrite IHt1. rewrite IHt3. rewrite IHt2. reflexivity. inversion HASTY; assumption. inversion HASTY; assumption. inversion HASTY; assumption.
  intros. induction T. inversion HASTY.  eauto.
  intros. induction T. simpl. inversion HASTY. simpl. apply IHt. inversion HASTY. apply H0.
  intros. induction T. inversion HASTY. simpl. apply IHt. inversion HASTY. apply H0.
  intros. induction T. simpl. apply IHt. inversion HASTY. apply H0.
  intros. inversion HASTY.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero)))
    TBool
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero)))
    TBool
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
