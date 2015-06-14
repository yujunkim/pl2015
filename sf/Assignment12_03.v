Require Export Assignment12_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (types_unique)  *)
(** Another pleasant property of the STLC is that types are
    unique: a given term (in a given context) has at most one
    type. *)

Lemma type_is_unique: forall t G T T'
    (TYPED: G |- t \in T)
    (TYPED': G |- t \in T'),
  T = T'.
Proof with eauto 12.


  intros.
  generalize dependent T.
  generalize dependent T'.
  generalize dependent G.
  t_cases (induction t) Case; intros; inversion TYPED; subst; clear TYPED; inversion TYPED'; subst; clear TYPED'...

  rewrite H1 in H2. inversion H2... eauto.

  apply IHt2 with (T' := T0) in H4...
  apply IHt1 with (T' := (TArrow T1 T)) in H3... inversion H3...

  apply IHt with (T' := T0) in H4... subst...

  apply IHt2 with (T' := T3) in H4...
  apply IHt1 with (T' := T1) in H3... subst...

  apply IHt with (T' := (TProd T' T0)) in H1... inversion H1...

  apply IHt with (T' := (TProd T0 T')) in H1... inversion H1...

  apply IHt1 with (T' := T0) in H4... subst...

  apply IHt with (T' := T0) in H3... rewrite H3...

  apply IHt with (T' := T0) in H3... rewrite H3...

  apply IHt1 with (T' := (TSum T0 T3)) in H6... subst... inversion H6. subst...

  apply IHt with (T' := (TArrow (TArrow T0 T3) (TArrow T0 T3))) in H1... inversion H1...
Qed.

(*-- Check --*)
Check type_is_unique: forall t G T T'
    (HTyped: G |- t \in T)
    (HTyped': G |- t \in T'),
  T = T'.

