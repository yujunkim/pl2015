Require Export Assignment12_04.

(* problem #05: 20 points *)

(** Translate this informal recursive definition into one using [fix]:
<<
   halve =
     \x:Nat.
        if x=0 then 0
        else if (pred x)=0 then 0
        else 1 + (halve (pred (pred x))))
>>
*)

Definition halve : tm :=
  tfix
    (tabs A (TArrow TNat TNat)
      (tabs B TNat
        (tif0 (tvar B)
           (tnat 0)
           (tif0 (tpred (tvar B))
             (tnat 0)
             (tsucc (tapp (tvar A) (tpred (tpred (tvar B)))))
           )
        )
      )
    ).

Example halve_type: empty |- halve \in TArrow TNat TNat.
Proof.
  unfold halve; eauto 10.
Qed.

Example halve_10: tapp halve (tnat 10) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.

Example halve_11: tapp halve (tnat 11) ==>* tnat 5.
Proof.
  unfold halve; normalize.
Qed.


Theorem halve_correct: forall n,
   tapp halve (tnat (n+n)) ==>* tnat n.
Proof with eauto.
  intros.
  induction n. unfold halve.  normalize.

  apply multi_trans with (y := (tsucc (tapp halve (tnat (n + n))))).
  unfold halve.
  eapply multi_step...
  eapply multi_step...
  eapply multi_step.
  apply ST_AppAbs... simpl.
  eapply multi_step...
  eapply multi_step... simpl.
  rewrite <- plus_n_Sm.
  eapply multi_step...
  eapply multi_step...



  apply multi_trans with (y := (tsucc (tnat n)))...
  induction IHn...
Qed.

(*-- Check --*)

Check conj halve_type (conj halve_10 halve_11) :
  empty |- halve \in TArrow TNat TNat /\
  tapp halve (tnat 10) ==>* tnat 5 /\
  tapp halve (tnat 11) ==>* tnat 5.

Check halve_correct: forall n,
   tapp halve (tnat (n + n)) ==>* tnat n.

