Require Export Assignment10_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
  apply multi_trans with (P (C 0) (P (C 2) (C (0 + 3)))).
  apply multi_R.
  try( apply ST_Plus1); try(apply ST_Plus2) ; try(apply ST_PlusConstConst); try(apply v_const).
  try( apply ST_Plus1); try(apply ST_Plus2) ; try(apply ST_PlusConstConst); try(apply v_const).
  apply multi_R.
  try( apply ST_Plus1); try(apply ST_Plus2) ; try(apply ST_PlusConstConst); try(apply v_const).
Qed.

(*-- Check --*)
Check test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).

