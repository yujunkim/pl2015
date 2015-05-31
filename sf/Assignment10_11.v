Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.

    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  induction t.
  intros.
  split. simpl. intros. rewrite H. constructor.
  intros. simpl. inversion H. reflexivity.
  intros. split. intros. inversion H. simpl. apply E_Plus. apply IHt1. reflexivity. apply IHt2. reflexivity.
  intros. simpl. inversion H. subst. replace (evalF t1) with n1. replace (evalF t2) with n2. reflexivity.
  symmetry. apply  IHt2. apply H4.
  symmetry. apply  IHt1. apply H2.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

