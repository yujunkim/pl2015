Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious.
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros.
  assert (H1: ev(n+m +(n +p))).
  - intros. apply ev_sum with(n:= n+m) (m:= n+p). apply H. apply H0.
  - rewrite plus_assoc in H1.
    rewrite <- plus_assoc with(n:=n)(m:=m)(p:=n) in H1.
    rewrite plus_comm with(n:=m)(m:=n) in H1.
    rewrite plus_assoc in H1.
    rewrite <- double_plus in H1.
    rewrite <- plus_assoc in H1.
    apply ev_ev__ev with(n:= double n) in H1.
    + apply H1.
    + apply double_even.
Qed.
(** [] *)


