Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }}
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }}
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  eapply hoare_seq with (fun st: state => st Y * fact (st X) = fact m).
  eapply hoare_consequence_post.
  apply hoare_while.
  eapply hoare_seq. apply hoare_asgn.
  eapply hoare_consequence_pre. apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_true in H1. apply beq_nat_false in H1. rewrite <- mult_assoc. replace (st X * fact (st X - 1)) with (fact (st X)). apply H0.
  destruct (st X). exfalso. apply H1. reflexivity.
  simpl. rewrite <- minus_n_O. reflexivity.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. inversion H. apply negb_false in H1. apply beq_nat_true in H1. rewrite H1 in H0. simpl in H0. SearchAbout mult. rewrite mult_1_r in H0. apply H0.

  eapply hoare_consequence_pre.
  apply hoare_asgn.

  unfold beval, assn_sub, update, assert_implies. simpl.
  intros. rewrite H. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }}
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

