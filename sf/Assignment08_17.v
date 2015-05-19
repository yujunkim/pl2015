Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. intros. induction b; simpl; try constructor.
  - rename a into a1.
    rename a0 into a2.
    remember (optimize_0plus_aexp a1) as a1'.
    remember (optimize_0plus_aexp a2) as a2'.
    unfold bequiv. intros. simpl.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    reflexivity.
    rewrite Heqa2'. rewrite <- optimize_0plus_aexp_sound. reflexivity.
    rewrite Heqa1'. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - rename a into a1.
    rename a0 into a2.
    remember (optimize_0plus_aexp a1) as a1'.
    remember (optimize_0plus_aexp a2) as a2'.
    unfold bequiv. intros. simpl.
    replace (aeval st a1) with (aeval st a1').
    replace (aeval st a2) with (aeval st a2').
    reflexivity.
    rewrite Heqa2'. rewrite <- optimize_0plus_aexp_sound. reflexivity.
    rewrite Heqa1'. rewrite <- optimize_0plus_aexp_sound. reflexivity.
  - unfold bequiv. intros. simpl. rewrite IHb. reflexivity.
  - unfold bequiv. intros. simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

