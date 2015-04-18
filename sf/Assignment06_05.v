Require Export Assignment06_04.

(* problem #05: 20 points *)

(** **** Exercise: 3 stars (all_forallb)  *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all {X : Type} (P : X -> Prop) : list X -> Prop :=
  | all_nil : all P []
  | all_later : forall b l, (all P l /\ P b) -> all P (b::l)
  (* FILL IN HERE *)
.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_correct: forall X (P: X -> bool) l,
  forallb P l = true <-> all (fun x => P x = true) l.
Proof.
  intros.
  unfold iff.
  split.
  - induction l.
    + simpl. intros. apply all_nil.
    + simpl. unfold andb. intros. destruct (P x) eqn:nn.
      apply all_later. split. apply IHl. apply H. apply nn.
      inversion H.
  - intros. induction l.
    + simpl. intros. reflexivity.
    + simpl. intros. destruct (P x) eqn:nn.
      unfold andb. apply IHl. inversion H. inversion H1. apply H3.
      inversion H. rewrite nn in H1. inversion H1. inversion H4.
Qed.

(** [] *)

