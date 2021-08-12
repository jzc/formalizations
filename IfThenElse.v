Require Import Decidable.
Require Import Relation_Operators.
Require Import Equality.

Inductive term : Set :=
| trueT : term
| falseT : term
| if_then_elseT : term -> term -> term -> term.


Inductive eval1 : term -> term -> Prop :=
| e_if_true : forall t2 t3, eval1 (if_then_elseT trueT t2 t3) t2
| e_if_false : forall t2 t3, eval1 (if_then_elseT falseT t2 t3) t3
| e_if : forall t1 t1' t2 t3,
    eval1 t1 t1' -> eval1 (if_then_elseT t1 t2 t3) (if_then_elseT t1' t2 t3).

Notation "t1 --> t2" := (eval1 t1 t2) (at level 70, no associativity).

Theorem eval1_deterministic : forall t t' t'',
    t --> t' -> t --> t'' -> t' = t''.
Proof.
  intros t t' t'' Ht'. generalize dependent t''.
  induction Ht' as [].
  - intros t'' Ht''. inversion Ht''. reflexivity.
    inversion H3.
  - intros t'' Ht''. inversion Ht''. reflexivity.
    inversion H3.
  - intros t'' Ht''. inversion Ht''. rewrite <- H0 in Ht'.
    inversion Ht'. rewrite <- H0 in Ht'.
    inversion Ht'. f_equal. apply IHHt'. auto.
Qed.

Inductive value : term -> Prop :=
| value_true : value trueT
| value_false : value falseT.

Lemma value_dec : forall t, decidable (value t).
Proof.
  unfold decidable. destruct t.
  - left. apply value_true.
  - left. apply value_false.
  - right. intros H. inversion H.
Qed.

Definition nf (t : term) : Prop := ~ exists t', t --> t'.

Theorem nf_value : forall t, value t <-> nf t.
Proof.
  intros t. split.
  - intros Hvt. inversion Hvt; intros [t' Ht']; inversion Ht'.
  - apply contrapositive. apply value_dec.
    induction t.
    + intros Hnv. exfalso. apply Hnv. apply value_true.
    + intros Hnv. exfalso. apply Hnv. apply value_false.
    + intros Hnv Hnf. destruct t1.
      * apply Hnf. exists t2. apply e_if_true.
      * apply Hnf. exists t3. apply e_if_false.
      * apply IHt1. intros Hv. inversion Hv.
        intros [t' Ht']. apply Hnf.
        exists (if_then_elseT t' t2 t3). apply e_if. auto.
Qed.
  
Notation "t1 -->* t2" := (clos_refl_trans_1n _ eval1 t1 t2) (at level 70).

Theorem multistep_nf_unique : forall t u u',
    t -->* u -> nf u -> t -->* u' -> nf u' -> u = u'.
Proof.
  intros t u u' Hu Hnfu. generalize dependent u'.
  induction Hu.
  - intros u' Hu' Hnfu'. inversion Hu'.
    reflexivity. exfalso. apply Hnfu.
    exists y. auto.
  - intros u' Hu' Hnfu'. inversion Hu'.
    exfalso. apply Hnfu'. exists y. rewrite <- H0. auto.
    apply IHHu. apply Hnfu.
    assert (Heq : y0 = y).
    { apply eval1_deterministic with (t:=x). auto. auto. }
    rewrite <- Heq. auto. auto.
Qed.

Fixpoint size (t : term) :=
  match t with
  | trueT => 1
  | falseT => 1
  | if_then_elseT t1 t2 t3 => 1 + (size t1) + (size t2) + (size t3)
  end.

Require Import PeanoNat.
Require Import Operators_Properties.

Lemma add_lt_l : forall m n p, m + n < p -> m < p.
Proof.
  intros m n p H.
  assert (H'': p <> 0).
  { unfold lt in H. inversion H. intros E. inversion E.
    intros E. inversion E. }
  unfold lt in H. apply Nat.le_succ_le_pred in H.
  assert (H' : m <= Nat.pred p).
  { transitivity (Nat.pred p - n).
    apply Nat.le_add_le_sub_r. apply H.
    apply Nat.le_sub_l. }
  unfold lt.
  rewrite <- (Nat.succ_pred).
  apply Nat.succ_le_mono in H'. apply H'. auto.
Qed.

Lemma multistep_cong_if : forall t1 t1' t2 t3,
    t1 -->* t1' -> if_then_elseT t1 t2 t3 -->* if_then_elseT t1' t2 t3.
Proof.
  intros t1 t1' t2 t3 Hev.
  induction Hev.
  - apply rt1n_refl.
  - apply e_if with (t2:=t2) (t3:=t3) in H.
    apply Relation_Operators.rt1n_trans with (y:=(if_then_elseT y t2 t3)).
    auto. auto.
Qed.

Lemma multistep_transitive : forall t1 t2 t3,
    t1 -->* t2 -> t2 -->* t3 -> t1 -->* t3.
Proof.
  intros t1 t2 t3 H12 H23. induction H12.
  - apply H23.
  - apply IHclos_refl_trans_1n in H23.
    apply Relation_Operators.rt1n_trans with (y:=y). auto. auto.
Qed.
    
Theorem normalizing : forall t, exists t', nf t' /\ t -->* t'.
Proof.
  pose (P:= fun n => forall t, size t = n -> exists t', nf t' /\ t-->* t').
  assert (H : forall n, P n).
  { apply (well_founded_ind Nat.lt_wf_0).
    unfold P.
    intros n IH.
    intros t Ht. destruct t as [].
    - exists trueT. split. apply nf_value. apply value_true.
      apply rt1n_refl.
    - exists falseT. split. apply nf_value. apply value_false.
      apply rt1n_refl.
    - simpl in Ht.
      assert (Hs : size t1 + size t2 + size t3 < n).
      { unfold lt. rewrite Ht. apply Nat.le_refl. }
      assert (Hs1: size t1 < n).
      { rewrite <- Nat.add_assoc in Hs.
        apply add_lt_l with (n:=(size t2 + size t3)). auto. }
      assert (Hs2: size t2 < n).
      { rewrite (Nat.add_comm (size t1)) in Hs.
        rewrite <- Nat.add_assoc in Hs.
        apply add_lt_l with (n:=(size t1 + size t3)). auto. }
      assert (Hs3: size t3 < n).
      { rewrite (Nat.add_comm _ (size t3)) in Hs.
        apply add_lt_l with (n:=(size t1 + size t2)). auto. }
      apply IH with (t:=t1) in Hs1.
      apply IH with (t:=t2) in Hs2.
      apply IH with (t:=t3) in Hs3.
      destruct Hs1 as [t1' [Hnft1' Hevt1']].
      destruct Hs2 as [t2' [Hnft2' Hevt2']].
      destruct Hs3 as [t3' [Hnft3' Hevt3']].
      apply nf_value in Hnft1'.
      apply multistep_cong_if with (t2:=t2) (t3:=t3) in Hevt1'.
      destruct Hnft1'.
      + exists t2'. split. auto.
        assert (Hevt2'' : if_then_elseT trueT t2 t3 -->* t2').
        { apply Relation_Operators.rt1n_trans with (y:=t2).
          apply e_if_true. auto. }
        apply multistep_transitive with (t2:=if_then_elseT trueT t2 t3).
        auto. auto.
      + exists t3'. split. auto.
        assert (Hevt3'' : if_then_elseT falseT t2 t3 -->* t3').
        { apply Relation_Operators.rt1n_trans with (y:=t3).
          apply e_if_false. auto. }
        apply multistep_transitive with (t2:=if_then_elseT falseT t2 t3).
        auto. auto.
      + reflexivity.
      + reflexivity.
      + reflexivity. }
  intros t. unfold P in H. apply H with (n:=size t). reflexivity.
Qed.
