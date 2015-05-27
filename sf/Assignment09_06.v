Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }}
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros.
  apply hoare_seq with (fun st: state => (st Y + st X = m)).


  eapply hoare_consequence_post.
  eapply hoare_while.
  eapply hoare_seq.
  apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  unfold beval, assn_sub, update, assert_implies.
  simpl.
  intros st [H1 H2]. apply negb_true in H2. apply beq_nat_false in H2. omega.

  unfold beval, assn_sub, update, assert_implies.
  intros. inversion H. apply negb_false in H1. apply beq_nat_true in H1. simpl in H1. omega.

  eapply hoare_consequence_pre. apply hoare_asgn.
  unfold assn_sub.
  simpl. unfold update. simpl. unfold assert_implies. intros. apply H.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.

