(* Require Import Coq.Lists.List. *)
(* Require Import Coq.Lists.ListSet. *)
Require Import List.
Import ListNotations.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Powerset.
Require Import PeanoNat.
Require Import Bool.

Inductive prop : Set :=
| Bot
| Var (x : nat)
| Not (p : prop)
| And (p1 p2 : prop)
| Or (p1 p2 : prop)
| Implies (p1 p2 : prop)
| Iff (p1 p2 : prop).

Fixpoint prop_eqb (p q : prop) : bool :=
  match p, q with 
  | Bot, Bot => true
  | Var x1, Var x2 => (Nat.eqb x1 x2)
  | Not p, Not q => (prop_eqb p q)
  | And p1 p2, And q1 q2 => (prop_eqb p1 q1) && (prop_eqb p2 q2)
  | Or p1 p2, Or q1 q2 => (prop_eqb p1 q1) && (prop_eqb p2 q2)
  | Implies p1 p2, Implies q1 q2 => (prop_eqb p1 q1) && (prop_eqb p2 q2)
  | Iff p1 p2, Iff q1 q2 => (prop_eqb p1 q1) && (prop_eqb p2 q2)
  | _, _ => false
  end.

Lemma prop_eqb_refl : forall p, prop_eqb p p = true.
Proof.
  induction p; try (
   try (reflexivity);
   try (simpl; apply Nat.eqb_refl);
   try (simpl; apply IHp);
   try (simpl; rewrite IHp1; rewrite IHp2; auto)).
Qed.               

Lemma prop_eqb_eq : forall p q, p = q <-> prop_eqb p q = true.
Proof.
  intros p q. split.
  - intros H. rewrite H. apply prop_eqb_refl.
  - generalize dependent q. induction p; destruct q; try discriminate.
    
    reflexivity.
    
    intros H; simpl in H; apply Nat.eqb_eq in H; f_equal; apply H.
    
    intros H; simpl in H; apply IHp in H; f_equal; apply H.

    intros H; simpl in H; apply andb_true_iff in H;
      destruct H as [H1 H2]; apply IHp1 in H1;
        apply IHp2 in H2; f_equal; try apply H1; try apply H2.

    intros H; simpl in H; apply andb_true_iff in H;
      destruct H as [H1 H2]; apply IHp1 in H1;
        apply IHp2 in H2; f_equal; try apply H1; try apply H2.

    intros H; simpl in H; apply andb_true_iff in H;
      destruct H as [H1 H2]; apply IHp1 in H1;
        apply IHp2 in H2; f_equal; try apply H1; try apply H2.

    intros H; simpl in H; apply andb_true_iff in H;
      destruct H as [H1 H2]; apply IHp1 in H1;
        apply IHp2 in H2; f_equal; try apply H1; try apply H2.

Qed.

Lemma prop_neqb_neq : forall p q, p <> q <-> prop_eqb p q = false.
  intros p q. split.
  - intros H. destruct (prop_eqb p q) as [] eqn:E.
    + apply prop_eqb_eq in E. apply H in E. contradiction.
    + auto.
  - intros H. destruct (prop_eqb p q) as [] eqn:E.
    + discriminate H.
    + intros H'.  rewrite H' in E. rewrite prop_eqb_refl in E.
      discriminate E.
Qed.
            
Definition valuation := nat -> bool.

Fixpoint interpret (v : valuation) (p : prop) : bool :=
  match p with
  | Bot => false
  | Var x => v x
  | Not p => negb (interpret v p)
  | And p1 p2 => andb (interpret v p1) (interpret v p2)
  | Or p1 p2 => orb (interpret v p1) (interpret v p2)
  | Implies p1 p2 => if interpret v p1 then interpret v p2 else true
  | Iff p1 p2 => (eqb (interpret v p1) (interpret v p2))
  end.

Definition propset := Ensemble prop.
Arguments In {U}.
Arguments Add {U}.
Arguments Subtract {U}.
Arguments Union {U}.
Arguments Setminus {U}.
Arguments Singleton {U}.
Arguments Empty_set {U}.
Arguments Finite {U}.
Arguments Included {U}.

Lemma Included_add : forall (U : Type) (A : Ensemble U) (a : U),
      Included A (Add A a).
Proof.
  intros U A a x Hx. apply Union_introl. apply Hx.
Qed.

Lemma Union_Included : forall U (A B : Ensemble U),
    Included A (Union A B) /\ Included B (Union A B).
Proof.
  intros U A B. split.
  - intros x Hx. apply Union_introl. apply Hx.
  - intros x Hx. apply Union_intror. apply Hx.
Qed.

Lemma Union_idempotent : forall U (A : Ensemble U),
    A = Union A A.
Proof.
  intros U A. apply Extensionality_Ensembles. split.
  - intros x Hx. apply Union_introl. apply Hx.
  - intros x Hx. inversion Hx. apply H. apply H.
Qed.  

Lemma Subtract_preserves_Finite : forall U (X : Ensemble U) (a : U),
    Finite X -> Finite (Subtract X a).
Proof.
  intros U X a H.
  assert (Hss : Included (Subtract X a) X).
  { unfold Included. intros x Hx. unfold In. unfold In in Hx.
    inversion Hx. apply H0. }
  apply Finite_downward_closed with (A:=X).
  apply H.
  apply Hss.
Qed.

Lemma Subtract_Add : forall (X : propset) (a : prop),
    X a -> Add (Subtract X a) a = X.
Proof.
  intros X a Ha. apply Extensionality_Ensembles. split.
  - intros x Hx. inversion Hx as [].
    + inversion H as []. apply H1.
    + inversion H as []. rewrite H1 in Ha. apply Ha.
  - intros x Hx. destruct (prop_eqb x a) as [] eqn:E.
    + apply prop_eqb_eq in E. unfold In.
      assert (Hsa: Add (Subtract X a) a a).
      { unfold Add. apply Union_intror. apply In_singleton. }
      rewrite E. apply Hsa.
    + assert (Hsx: (Subtract X a) x).
      { unfold Subtract. unfold Setminus. split.
        apply Hx. intros Hisa. inversion Hisa.
        rewrite H in E. rewrite prop_eqb_refl in E.
        discriminate E. }
      apply Union_introl. apply Hsx.
Qed.

Definition holds (v : valuation) (p : prop) : Prop := interpret v p = true.

Definition satisfies (v : valuation) (gamma : propset) : Prop :=
  forall q, gamma q -> holds v q.

Definition entails (gamma : propset) (p : prop) : Prop :=
  forall v, satisfies v gamma -> holds v p.

Lemma satisfies_holds_in : forall v gamma p, satisfies v gamma -> gamma p -> holds v p.
Proof.
  intros v gamma p Hsvg Hgp. apply Hsvg. apply Hgp.
Qed.

Lemma satisfies_union : forall v gamma1 gamma2,
    satisfies v (Union gamma1 gamma2) -> satisfies v gamma1 /\ satisfies v gamma2.
Proof.
  intros v gamma1 gamma2 H. split.
  - intros p Hp. apply satisfies_holds_in with (gamma:=Union gamma1 gamma2).
    apply H. apply Union_introl. apply Hp.
  - intros p Hp. apply satisfies_holds_in with (gamma:=Union gamma1 gamma2).
    apply H. apply Union_intror. apply Hp.
Qed.

Lemma entails_in : forall p (gamma : propset),
    gamma p -> entails gamma p.
Proof.
  intros p gamma H v Hv. apply satisfies_holds_in with (gamma:=gamma).
  apply Hv. apply H.
Qed.

Lemma entails_and_intro : forall p q gamma1 gamma2,
    entails gamma1 p /\ entails gamma2 q -> entails (Union gamma1 gamma2) (And p q).
Proof.
  intros p q gamma1 gamma2 [Hg1 Hg2] v Hv.
  apply satisfies_union in Hv.
  assert (H1 : holds v p).
  { apply Hg1. apply Hv. }
  assert (H2 : holds v q).
  { apply Hg2. apply Hv. }
  unfold holds. simpl. rewrite H1. rewrite H2. auto.
Qed.

Lemma entails_and_elim : forall p q gamma,
    entails gamma (And p q) -> entails gamma p /\ entails gamma q.
Proof.
  intros p q gamma H.
  assert (H': forall v, satisfies v gamma -> holds v p /\ holds v q).
  { intros v Hv. apply H in Hv. unfold holds in Hv. simpl in Hv.
    apply andb_true_iff. apply Hv. }
  split.
  - intros v. apply H'.
  - intros v. apply H'.
Qed.

Lemma entails_implies_intro : forall p q gamma,
    entails (Add gamma p) q -> entails gamma (Implies p q).
Proof.
  intros p q gamma H v Hv. unfold holds. simpl.
  destruct (interpret v p) as [] eqn:E.
  - assert (H': satisfies v (Add gamma p)).
    { intros q' Hq'. inversion Hq' as [].
      - apply satisfies_holds_in with (gamma:=gamma). apply Hv. apply H0.
      - inversion H0 as []. rewrite H2 in E. apply E. }
    apply H in H'. apply H'.
  - auto.
Qed.

Lemma entails_implies_elim : forall p q gamma1 gamma2,
    entails gamma1 p -> entails gamma2 (Implies p q) -> entails (Union gamma1 gamma2) q.
Proof.
  intros p q gamma1 gamma2 Hep Hepq v Hv.
  apply satisfies_union in Hv. destruct Hv as [Hv1 Hv2].
  apply Hep in Hv1. apply Hepq in Hv2.
  unfold holds in Hv1. unfold holds in Hv2.
  simpl in Hv2. rewrite Hv1 in Hv2. apply Hv2.
Qed.

Lemma entails_bot : forall p gamma,
    entails gamma Bot -> entails gamma p.
Proof.
  intros p gamma H v Hv. apply H in Hv.
  unfold holds in Hv. simpl in Hv. discriminate Hv.
Qed.

Lemma entails_double_not : forall p gamma,
    entails gamma (Implies (Implies p Bot) Bot)
    -> entails gamma p.
Proof.
  intros p gamma H v Hv.
  apply H in Hv. unfold holds in Hv. simpl in Hv.
  destruct (interpret v p) as [] eqn:E.
  - apply E.
  - discriminate Hv.
Qed.

Inductive derivation :  propset -> prop -> Type :=
| d_assume : forall (gamma : propset) p , gamma p -> derivation gamma p
| d_andintro : forall gamma1 gamma2 p1 p2,
    derivation gamma1 p1 -> derivation gamma2 p2 ->
    derivation (Union gamma1 gamma2) (And p1 p2)
| d_andeliml : forall gamma p1 p2,
    derivation gamma (And p1 p2) -> derivation gamma p1
| d_andelimr : forall gamma p1 p2,
    derivation gamma (And p1 p2) -> derivation gamma p2
| d_impliesintro : forall gamma p1 p2,
    derivation (Add gamma p1) p2 -> derivation gamma (Implies p1 p2)
| d_implieselim : forall gamma1 gamma2 p1 p2,
    derivation gamma1 p1 -> derivation gamma2 (Implies p1 p2)
    -> derivation (Union gamma1 gamma2) p2
| d_absurd : forall gamma p,
    derivation gamma Bot -> derivation gamma p
| d_raa : forall gamma p,
    derivation (Add gamma (Implies p Bot)) Bot -> derivation gamma p.

Theorem soundness : forall gamma p, derivation gamma p -> entails gamma p.
Proof.
  intros gamma p Hdp. induction Hdp.
  - apply entails_in. auto.
  - apply entails_and_intro. auto.
  - apply entails_and_elim in IHHdp. destruct IHHdp as [H _]. apply H.
  - apply entails_and_elim in IHHdp. destruct IHHdp as [_ H]. apply H.
  - apply entails_implies_intro. auto.
  - apply entails_implies_elim with (p:=p1). auto. auto.
  - apply entails_bot. auto.
  - apply entails_implies_intro in IHHdp.
    apply entails_double_not. auto.
Qed.

Fixpoint assumptions (gamma : propset) (p : prop) (d: derivation gamma p) : propset :=
  match d with
  | d_assume gamma' p' Hin        => Singleton p'
  | d_andintro _ _ _ _ d1' d2'    => Union (assumptions _ _ d1') (assumptions _ _ d2')
  | d_andeliml _ _ _ d'           => assumptions _ _ d'
  | d_andelimr _ _ _ d'           => assumptions _ _ d'
  | d_impliesintro _ p1' _ d'     => Subtract (assumptions _ _ d') p1'
  | d_implieselim _ _ _ _ d1' d2' => Union (assumptions _ _ d1') (assumptions _ _ d2')
  | d_absurd _ _ d                => assumptions _ _ d
  | d_raa _ p d                   => Subtract (assumptions _ _ d) (Implies p Bot)
  end.


Lemma weaken : forall (gamma gamma' : propset) p (d : derivation gamma p),
    Included gamma gamma' -> derivation gamma' p.
Proof.
  intros gamma gamma' p d. generalize dependent gamma'. induction d.
  - intros gamma' H. apply d_assume. apply H. apply g.
  - intros gamma' H.
    assert (H1 : Included gamma1 gamma').
    { assert (H'1: Included gamma1 (Union gamma1 gamma2)).
      { apply Union_Included. }
      intros x Hx. apply H. apply H'1. apply Hx. }
    assert (H2 : Included gamma2 gamma').
    { assert (H'1: Included gamma2 (Union gamma1 gamma2)).
      { apply Union_Included. }
      intros x Hx. apply H. apply H'1. apply Hx. }
    apply IHd1 in H1. apply IHd2 in H2.
    assert (H3 : gamma' = Union gamma' gamma').
    { apply Union_idempotent. }
    rewrite H3. apply d_andintro. apply H1. apply H2.
  - intros gamma' H. apply IHd in H. apply d_andeliml with (p2:=p2). apply H.
  - intros gamma' H. apply IHd in H. apply d_andelimr with (p1:=p1). apply H.
  - intros gamma' H. apply d_impliesintro. apply IHd.
    intros x Hx. inversion Hx.
    + apply H in H0. apply Union_introl. apply H0.
    + apply Union_intror. apply H0.
  - intros gamma' H.
    assert (H1 : Included gamma1 gamma').
    { assert (H'1: Included gamma1 (Union gamma1 gamma2)).
      { apply Union_Included. }
      intros x Hx. apply H. apply H'1. apply Hx. }
    assert (H2 : Included gamma2 gamma').
    { assert (H'1: Included gamma2 (Union gamma1 gamma2)).
      { apply Union_Included. }
      intros x Hx. apply H. apply H'1. apply Hx. }
    apply IHd1 in H1. apply IHd2 in H2.
    assert (H3 : gamma' = Union gamma' gamma').
    { apply Union_idempotent. }
    rewrite H3. apply d_implieselim with (p1:=p1). apply H1. apply H2.
  - intros gamma' H. apply IHd in H. apply d_absurd. apply H.
  - intros gamma' H. apply d_raa. apply IHd.
    intros x Hx. inversion Hx.
    + apply H in H0. apply Union_introl. apply H0.
    + apply Union_intror. apply H0.
Qed.   


Theorem assumptions_finite : forall gamma p (d : derivation gamma p),
    Finite (assumptions _ _ d).
Proof.
  intros gamma p d. induction d.
  - simpl. apply Singleton_is_finite.
  - simpl. apply Union_preserves_Finite. auto. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. apply Subtract_preserves_Finite. auto.
  - simpl. apply Union_preserves_Finite. auto. auto.
  - simpl. auto.
  - simpl. apply Subtract_preserves_Finite. auto.
Qed.


Theorem assumption_derivation (gamma : propset) (p : prop) (d : derivation gamma p)
  : derivation (assumptions _ _ d) p.
Proof.
  induction d as [].
  - simpl. apply d_assume. apply In_singleton.
  - simpl. apply d_andintro. auto. auto.
  - simpl. apply d_andeliml with (p2:=p2). apply IHd.
  - simpl. apply d_andelimr with (p1:=p1). apply IHd.
  - simpl. apply d_impliesintro.
    remember (assumptions (Add gamma p1) p2 d) as A.
    assert (H1 : Included A (Add (Subtract A p1) p1 )).
    { intros x Hx. destruct (prop_eqb p1 x) as [] eqn:E.
      - apply Union_intror. apply prop_eqb_eq in E.
        rewrite E. apply In_singleton.
      - apply Union_introl. unfold Subtract.
        unfold Setminus. unfold In. split.
        + apply Hx.
        + intros nH. inversion nH. rewrite H in E.
          rewrite prop_eqb_refl in E. discriminate E. }
    apply weaken with (gamma:=A). apply IHd. apply H1.
  - simpl. apply d_implieselim with (p1:=p1). apply IHd1. apply IHd2.
  - simpl. apply d_absurd. apply IHd.
  - simpl. apply d_raa.
    remember (assumptions (Add gamma (Implies p Bot)) Bot d) as A.
    assert (H1 : Included A (Add (Subtract A (Implies p Bot)) (Implies p Bot))).
    { intros x Hx. destruct (prop_eqb (Implies p Bot) x) as [] eqn:E.
      - apply Union_intror. apply prop_eqb_eq in E.
        rewrite E. apply In_singleton.
      - apply Union_introl. unfold Subtract.
        unfold Setminus. unfold In. split.
        + apply Hx.
        + intros nH. inversion nH. rewrite H in E.
          rewrite prop_eqb_refl in E. discriminate E. }
    apply weaken with (gamma:=A). apply IHd. apply H1.
Qed.

Definition derivable (gamma : propset) (p : prop) : Prop :=
  inhabited (derivation gamma p).

Definition consistent (gamma : propset) : Prop := 
  ~ (derivable gamma Bot).

Definition satisfiable (gamma : propset) : Prop := exists v, satisfies v gamma.

Theorem satisfiable_consistent : forall gamma,
    satisfiable gamma -> consistent gamma.
Proof.
  intros gamma [v Hv]. unfold consistent. intros [db]. apply soundness in db.
  unfold entails in db.
  apply db in Hv. unfold holds in Hv. simpl in Hv.
  discriminate.
Qed.

Lemma Included_consistent : forall gamma gamma',
    consistent gamma -> Included gamma' gamma
    -> consistent gamma'.
Proof.
  intros gamma gamma' Hc Hincl.
  intros [db]. apply weaken  with (gamma':=gamma) in db.
  apply inhabits in db. apply Hc in db. contradiction.
  apply Hincl.
Qed.


Lemma consistent_expansion_p : forall gamma p,
    consistent gamma -> ~ derivable gamma p
    -> consistent (Add gamma (Implies p Bot)).
Proof.
  intros gamma p Hc Hndp.
  intros [dnp]. apply d_raa in dnp.
  apply inhabits in dnp. apply Hndp in dnp.
  contradiction.
Qed.

Lemma consistent_expansion_np : forall gamma p,
    consistent gamma -> ~ derivable gamma (Implies p Bot)
    -> consistent (Add gamma p).
Proof.
  intros gamma p Hc Hndp.
  intros [dnp]. apply d_impliesintro in dnp.
  apply inhabits in dnp. apply Hndp in dnp.
  contradiction.
Qed.

Lemma Finite_derivable : forall gamma,
    Finite gamma -> (exists q, forall p, derivable gamma p <-> derivable (Singleton q) p).
Proof.
  intros gamma Hf. 
  induction Hf.
  - exists (Implies Bot Bot). intros p. split.
    + intros [dp]. apply inhabits. apply weaken with (gamma:=Empty_set).
      apply dp. intros x Hx. inversion Hx.
    + intros [dp]. apply inhabits.
      assert (Hs : Singleton (Implies Bot Bot) = (Add Empty_set (Implies Bot Bot))).
      { apply Extensionality_Ensembles. split.
        - intros x Hx. apply Union_intror. apply Hx.
        - intros x Hx. inversion Hx. inversion H. apply H. }
      rewrite Hs in dp. apply d_impliesintro in dp.
      assert (Hu : @Empty_set prop = @Union prop Empty_set Empty_set).
      { apply Union_idempotent. }
      rewrite Hu. apply d_implieselim with (p1:=(Implies Bot Bot)).
      apply d_impliesintro. apply d_assume. apply Union_intror.
      apply In_singleton.
      apply dp.
  - destruct IHHf as [q Hq].
    exists (And x q). intros p. split.
    + intros [dp]. apply d_impliesintro in dp.     
      apply inhabits in dp. apply Hq in dp.
      destruct dp as [dp].
      assert (Hs : Singleton q = Add Empty_set q).
      { apply Extensionality_Ensembles. split.
        - intros y Hy. apply Union_intror. apply Hy.
        - intros y Hy. inversion Hy. inversion H0. apply H0. }
      rewrite Hs in dp. apply d_impliesintro in dp.
      assert (dq : derivation (Singleton (And x q)) q).
      { apply d_andelimr with (p1:=x). apply d_assume.
        apply In_singleton. }
      assert (dxp : derivation (Singleton (And x q)) (Implies x p)).
      { rewrite <- (Empty_set_zero_right _ (Singleton (And x q))).
        apply d_implieselim with (p1:=q). apply dq. apply dp. }
      rewrite (Union_idempotent _ (Singleton (And x q))).
      apply inhabits. apply d_implieselim with (p1:=x).
      apply d_andeliml with (p2:=q). apply d_assume. apply In_singleton.
      apply dxp.
    + intros [dp]. Abort.
      

    
    
  
(* And, implies, bot, variable fragment *)
Inductive aibv_fragment : prop -> Prop :=
| Var_aibv (x : nat) : aibv_fragment (Var x)
| Bot_aibv : aibv_fragment Bot
| And_aibv (p1 : prop) (Hp1 : aibv_fragment p1)
  (p2 : prop) (Hp2 : aibv_fragment p2) : aibv_fragment (And p1 p2)
| Implies_aibv (p1 : prop) (Hp1 : aibv_fragment p1)
  (p2 : prop) (Hp2 : aibv_fragment p2) : aibv_fragment (Implies p1 p2).

Section em.

  Axiom strong_em : forall (P : Prop), {P} + {~ P}.

  Definition consistent_vars (gamma : propset) (p : prop) : Prop :=
    match p with
    | Var x => derivable gamma (Var x)
    | Implies (Var x) Bot => ~ derivable gamma (Var x)
    | _ => False
    end.

  Definition star (gamma : propset) : propset := derivable (consistent_vars gamma).

  Lemma complete_lemma_and : forall gamma p q,
      (derivable gamma p \/ derivable gamma (Implies p Bot))
      -> (derivable gamma q \/ derivable gamma (Implies q Bot))
      -> (derivable gamma (And p q) \/ derivable gamma (Implies (And p q) Bot)).
  Proof.
    intros gamma p q Hp Hq.
    destruct (Hp, Hq) as [[[dp] | [dnp]] [[dq] | [dnq]]].
    - left.
      assert (H: gamma = Union gamma gamma). { apply Union_idempotent. } rewrite H.
      apply inhabits. apply d_andintro. apply dp. apply dq.
    - right. apply inhabits. apply d_impliesintro.
      remember gamma as A. remember (Add A (And p q)) as A'.    
      assert (H: A' = Union A' A'). { apply Union_idempotent. } rewrite H.
      apply d_implieselim with (p1:=q).
      apply d_andelimr with (p1:=p). apply d_assume.
      rewrite HeqA'. apply Union_intror. apply In_singleton.
      apply weaken with (gamma:=A). apply dnq.
      rewrite HeqA'. apply Included_add.
    - right. apply inhabits. apply d_impliesintro.
      remember gamma as A. remember (Add A (And p q)) as A'.    
      assert (H: A' = Union A' A'). { apply Union_idempotent. } rewrite H.
      apply d_implieselim with (p1:=p).
      apply d_andeliml with (p2:=q). apply d_assume.
      rewrite HeqA'. apply Union_intror. apply In_singleton.
      apply weaken with (gamma:=A). apply dnp.
      rewrite HeqA'. apply Included_add.
    - right. apply inhabits. apply d_impliesintro.
      remember gamma as A. remember (Add A (And p q)) as A'.    
      assert (H: A' = Union A' A'). { apply Union_idempotent. } rewrite H.
      apply d_implieselim with (p1:=p).
      apply d_andeliml with (p2:=q). apply d_assume.
      rewrite HeqA'. apply Union_intror. apply In_singleton.
      apply weaken with (gamma:=A). apply dnp.
      rewrite HeqA'. apply Included_add.
  Qed.

  Lemma complete_lemma_implies : forall gamma p q,
      (derivable gamma p \/ derivable gamma (Implies p Bot))
      -> (derivable gamma q \/ derivable gamma (Implies q Bot))
      -> (derivable gamma (Implies p q) \/ derivable gamma (Implies (Implies p q) Bot)).
  Proof.
    intros gamma p q Hp Hq.
    destruct (Hp, Hq) as [[[dp] | [dnp]] [[dq] | [dnq]]].
    - left. apply inhabits. apply d_impliesintro.
      apply weaken with (gamma:=gamma). apply dq. apply Included_add.
    - right. apply inhabits. apply d_impliesintro.
      assert (dq : derivation (Add gamma (Implies p q)) q).
      { apply d_implieselim with (p1:=p). apply dp.
        apply d_assume. apply In_singleton. }
      assert (Hu: Add gamma (Implies p q) = Union (Add gamma (Implies p q))
                                                  (Add gamma (Implies p q))).
      { apply Union_idempotent. }
      rewrite Hu. apply d_implieselim with (p1:=q).
      apply dq. apply weaken with (gamma:=gamma). apply dnq.
      apply Included_add.
    - left. apply inhabits. apply d_impliesintro.
      apply weaken with (gamma:=gamma). apply dq. apply Included_add.
    - left. apply inhabits. apply d_impliesintro.
      apply d_absurd.
      assert (Hu: Add gamma p = Union (Add gamma p) (Add gamma p)).
      { apply Union_idempotent. } rewrite Hu.
      apply d_implieselim with (p1:=p). apply d_assume.
      apply Union_intror. apply In_singleton.
      apply weaken with (gamma:=gamma). apply dnp.
      apply Included_add.
  Qed.      
        
  Lemma gamma_star_complete : forall p gamma,
      aibv_fragment p -> star gamma p \/ star gamma (Implies p Bot).
  Proof.
    intros p gamma. induction p.
    - intros Hp. right. unfold star. apply inhabits.
      apply d_impliesintro. apply d_assume.
      apply Union_intror. apply In_singleton.
    - intros Hp.
      destruct (strong_em (derivable gamma (Var x))) as [Hd | Hnd].
      + left. apply inhabits. apply d_assume. apply Hd.
      + right. apply inhabits. apply d_assume. apply Hnd.
    - intros Hp. inversion Hp.
    - intros Hp. inversion Hp.
      apply IHp1 in Hp1. apply IHp2 in Hp2.
      apply complete_lemma_and. apply Hp1. apply Hp2.
    - intros Hp. inversion Hp.
    - intros Hp. inversion Hp.
      apply IHp1 in Hp1. apply IHp2 in Hp2.
      apply complete_lemma_implies. apply Hp1. apply Hp2.
    - intros Hp. inversion Hp.
  Qed.

  Lemma gamma_star_minus_gamma : forall gamma p,
      Setminus (star gamma) (derivable gamma) p ->
      ~ derivable gamma p /\ ~ derivable gamma (Implies p Bot).
  Proof.
    intros gamma p Hp. unfold Setminus in Hp.
    (* unfold star in Hp. *)
    unfold In in Hp. destruct Hp as [gsp ngp]. split.
    - intros ndp. apply ngp in ndp. contradiction.
    - intros ndnp. Abort.

  Lemma Setminus_intro : forall U (A B : Ensemble U),
      Included B A -> A = Union B (Setminus A B).
  Proof.
    intros U A B Hincl. apply Extensionality_Ensembles. split.
    - intros x Hx. destruct (strong_em (B x)).
      + apply Union_introl. apply b.
      + apply Union_intror. split. apply Hx. apply n.
    - intros x Hx. inversion Hx. apply Hincl in H. apply H.
      apply H.
  Qed.

  Definition derivable_vars (gamma : propset) (p : prop) : Prop :=
    match p with
    | Var x => derivable gamma p
    | Implies (Var x) Bot => derivable gamma (Implies (Var x) Bot)
    | _ => False
    end.

  (* if gamma were not consistent, then every for every n,
     x_n and ~ x_n and would be in derivable vars;
     consistent has has exactly one of x_n or ~ x_n *)
  Lemma derivable_vars_included : forall gamma,
      consistent gamma -> 
      Included (derivable_vars gamma) (consistent_vars gamma).
  Proof.
    intros gamma Hc x Hx. unfold In. unfold In in Hx.
    (* unfold consistent_vars. unfold derivable_vars in Hx. *)
    destruct x.
    - contradiction.
    - apply Hx.
    - contradiction.
    - contradiction.
    - contradiction.
    - destruct x1; destruct x2; try contradiction.
      simpl. simpl in Hx. intros [dx]. destruct Hx as [dnx].
      assert (db : derivation gamma Bot).
      { rewrite (Union_idempotent _ gamma).
        apply d_implieselim with (p1:=(Var x)).
        apply dx. apply dnx. }
      apply inhabits in db. apply Hc in db. contradiction.
    - contradiction.
  Qed.

  Lemma derivable_vars_derivable : forall gamma,
      consistent gamma -> (forall p, gamma p -> aibv_fragment p) ->
      derivable gamma = derivable (derivable_vars gamma).
  Proof.
    intros gamma Hc Haibv. apply Extensionality_Ensembles. split.
    - intros p. induction p.
      + intros [db]. apply inhabits in db. apply Hc in db. contradiction.
      + intros [dx]. apply inhabits. apply d_assume. simpl.
        apply inhabits. apply dx.
      + intros Hp.

    
    - intros Hb. 
      assert (db : derivation gamma Bot).
      { apply d_assume. apply Hb. }
      apply inhabits in db. apply Hc in db. contradiction.
    - intros Hx. apply inhabits. apply d_assume.
      simpl. apply inhabits. apply d_assume. apply Hx.
    - intros Hp. apply Haibv in Hp. inversion Hp.
    - intros Hp. Abort.
    
  Lemma Included_gamma_star : forall gamma,
      Included gamma (star gamma).
  Proof.
    intros gamma x Hx. unfold star. 
n    
  Lemma gamma_star_consistent : forall gamma,
      consistent gamma -> consistent (star gamma).
  Proof.
    intros gamma Hc. intros H.
    unfold consistent in Hc.
    
      

  Definition star_valuation (gamma : propset) (x : nat) : bool :=
    if (strong_em (star gamma (Var x)))
    then true
    else false.

  Lemma star_valuation_satisfies : forall gamma p,
      consistent gamma ->
      star gamma p <-> interpret (star_valuation gamma) p = true.
  Proof.
    intros gamma p Hc. induction p.
    - split.
      + intros H. unfold star in H.
        unfold consistent in Hc.
      
      
  Theorem consistent_satisfiable : forall gamma,
      consistent gamma -> satisfiable gamma.
  Proof.  Abort.        
          
End em.

