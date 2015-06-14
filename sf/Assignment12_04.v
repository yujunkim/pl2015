Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').
Proof with eauto 12.
  intros t t' T Hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.

  apply progress in Hhas_type... inversion Hhas_type...
  apply IHHmulti...

  apply preservation with (t':= y) in Hhas_type...
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T ->
  t ==>* t' ->
  ~(stuck t').

