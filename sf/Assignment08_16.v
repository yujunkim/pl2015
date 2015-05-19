Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.

  unfold atrans_sound. intros. unfold aequiv. intros. induction a; try constructor; try( simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  simpl. destruct a1.
  destruct a2;
    try destruct n; try destruct n0; simpl; try omega;
    try(simpl in IHa2; rewrite IHa2; reflexivity).
  destruct a2;
    try destruct n; try destruct n0; simpl; try omega;
    try(simpl in IHa2; rewrite IHa2; reflexivity).
  destruct a2;
    try (rewrite IHa1; rewrite IHa2; simpl; reflexivity);
    destruct n;
      try(rewrite IHa1; reflexivity);
      try( rewrite <- IHa1; simpl; omega).
  destruct a2;
    try (rewrite IHa1; rewrite IHa2; simpl; reflexivity);
    destruct n;
      try(rewrite IHa1; reflexivity);
      try( rewrite <- IHa1; simpl; omega).
  destruct a2;
    try (rewrite IHa1; rewrite IHa2; simpl; reflexivity);
    destruct n;
      try(rewrite IHa1; reflexivity);
      try( rewrite <- IHa1; simpl; omega).
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

