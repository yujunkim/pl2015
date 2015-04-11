Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)

    - Prove [pal_app_rev] that
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_X : forall x, pal [x]
  | pal_Y : forall x w, pal w  -> pal(x :: w ++ [x])
(* FILL IN HERE *)
.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  assert(H1 : forall X (x: X) (l : list X), snoc l x = l ++ [x]).
  - intros. induction l.
    + simpl. reflexivity.
    + simpl. rewrite IHl. reflexivity.
  - intros. induction l.
    + simpl. apply pal_nil.
    + assert(H2: forall X (l1 l2 l3 : list X), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3).
      intros. induction l1. reflexivity. simpl. rewrite IHl1.  reflexivity.
    simpl. specialize (H1 X x (rev l)). rewrite H1. rewrite H2 with(l1:=l)(l2:=rev l)(l3:= [x]). apply pal_Y with(w:=(l ++ rev l)). apply IHl.
Qed.

Theorem pal_H1: forall X (x: X) (l : list X),
  snoc l x = l ++ [x].
Proof.
  intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. reflexivity.
Qed.

Theorem pal_H2: forall X (x: X) (l : list X),
  x :: (rev l) = rev(l ++ [x]).
Proof.
  intros. induction l.
    - reflexivity.
    - simpl. rewrite pal_H1. rewrite pal_H1. rewrite <- IHl. reflexivity.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros. induction H.
    - reflexivity.
    - reflexivity.
    - simpl. rewrite pal_H1. rewrite <- pal_H2. rewrite <- IHpal. reflexivity.
Qed.

(** [] *)




