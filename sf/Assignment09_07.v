Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros.
  eapply hoare_consequence_pre with (fun st: state => st X + st Y = n + m).
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold beval, assn_sub, update, assert_implies. simpl. intros. inversion H. inversion H0. apply negb_true in H1. apply beq_nat_false in H1. omega.

  unfold beval, assn_sub, update, assert_implies. simpl. intros. inversion H. inversion H0. apply negb_false in H1. apply beq_nat_true in H1. omega.


  unfold assert_implies. intros. inversion H. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

