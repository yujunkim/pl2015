Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros.
  induction l1.
  - simpl. reflexivity.
  - simpl. rewrite <- IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  - exists []. exists l. reflexivity.
  - destruct IHappears_in. destruct proof. rewrite proof. exists (b::witness). exists witness0. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | re_first : forall l x, appears_in x l -> repeats (x::l)
  | re_step : forall l x, repeats l -> repeats (x::l).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma ai_comm : forall{X:Type} (l1 l2:list X) (x:X),
  appears_in x(l1++l2)->appears_in x(l2++l1).
Proof.
  intros. apply app_appears_in. apply or_commut. apply appears_in_app. apply H.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, appears_in x l1 -> appears_in x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.

  intros X l1. induction l1 as [|x l1'].
    intros. inversion H1.
    intro l2. unfold excluded_middle. intro em. destruct (em (appears_in x l1')).

      intros. apply re_first. apply H.
      intros. destruct (appears_in_app_split X x l2).
        apply H0. apply ai_here. destruct proof.
        intros. apply re_step. apply IHl1' with (witness++witness0).
          unfold excluded_middle. apply em.
          intros. assert(appears_in x0 l2). apply H0. apply ai_later. apply H2.
            destruct (em (x=x0)).
              elimtype False. apply H. rewrite H4. apply H2.
              rewrite proof in H3. apply ai_comm in H3. simpl in H3. apply ai_comm.
                inversion H3. elimtype False. apply H4. symmetry. apply H6. apply H6.
          rewrite proof in H1. rewrite app_length in H1. simpl in H1. rewrite <- plus_n_Sm in H1. unfold lt in H1. apply Sn_le_Sm__n_le_m. rewrite app_length. apply H1.
Qed.

