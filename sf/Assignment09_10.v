Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  eapply hoare_seq with (fun st: state => st X = 0).
  eapply hoare_seq with (fun st: state => st X = 0 /\st Y = 0).
  eapply hoare_seq with (fun st: state => st Z = (st X + c) /\ st Y = 0).
  eapply hoare_seq with (fun st: state => st Z = (a + st Y + c)).

  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_true in H1. apply beq_nat_false in H1. rewrite H0. omega.
  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_false in H1. apply beq_nat_true in H1. rewrite H0. omega.


  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_true in H1. apply beq_nat_false in H1. split. inversion H0. rewrite H2. omega. inversion H0. apply H3.
  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_false in H1. apply beq_nat_true in H1. inversion H0. rewrite H2. omega.


  eapply hoare_consequence_pre.
  apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. split. omega. omega.

  eapply hoare_consequence_pre.
  apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. split. omega. omega.

  eapply hoare_consequence_pre.
  apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. omega.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

