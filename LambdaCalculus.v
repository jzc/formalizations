Require Import Coq.MSets.MSets.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Definition var := nat.

Definition varset := list nat.
Definition inb (v : var) (X : varset) : bool := existsb (Nat.eqb v) X.
Definition singleton (v : var) : varset := v :: nil.
Definition empty : varset := nil.
Definition remove (v : var) (X : varset) : varset := remove Nat.eq_dec v X.
Definition union (X Y : varset) : varset := X ++ Y.
Definition intersect (X Y : varset) : varset := filter (fun x => inb x Y) X.

Lemma singleton_inb : forall v, (inb v (singleton v)) = true.
Proof. intros v. simpl. rewrite Nat.eqb_refl. simpl. reflexivity. Qed.

Lemma in_inb : forall v X, (inb v X = true) <-> (In v X).
Proof.
  intros v. induction X as [| x X' IH].
  - split.
    * simpl. intros. discriminate.
    * simpl. intros [].
  - split.
    + simpl. destruct (v =? x) as [] eqn:E.
      * intros _. left. apply Nat.eqb_eq. rewrite Nat.eqb_sym. apply E.
      * intros H. rewrite Bool.orb_false_l in H. apply IH in H.
        right. apply H.
    + simpl. intros [Hxv | HInvX'].
      * rewrite Hxv. rewrite Nat.eqb_refl. simpl. reflexivity.
      * apply IH in HInvX'. rewrite HInvX'. rewrite Bool.orb_true_r. reflexivity.
Qed.

Lemma intersect_in : forall v X Y, In v (intersect X Y) <-> In v X /\ In v Y.
Proof.
  intros v. induction X as [|v' X' IH].
  - intros Y. simpl. split.
    * intros H. contradiction.
    * intros [[] _].
  - intros Y. simpl. split.
    + intros H. destruct (inb v' Y) as [] eqn:E.
      * apply in_inb in E. simpl in H. destruct H as [H1|H2].
        -- split. left. apply H1. rewrite <- H1. apply E.
        -- split. right.  apply IH with Y. apply H2. apply (IH Y). apply H2.
      * split. right. apply IH with Y. auto. apply (IH Y). auto.
    + intros H. destruct H as [[H1|H2] H3].
      * rewrite H1. apply in_inb in H3. rewrite H3. simpl. auto.
      * destruct (inb v' Y) as [] eqn:E.
        -- simpl. right. apply IH. auto.
        -- simpl. apply IH. auto.
Qed.

Lemma union_in : forall v X Y, In v (union X Y) <-> In v X \/ In v Y.
Proof.
  intros v X Y. unfold union. apply in_app_iff.
Qed.
          
Lemma notin_remove : forall v X, inb v (remove v X) = false.
Proof.
  intros v X. assert (H: ~ (In v (remove v X))). apply remove_In.
  destruct (inb v (remove v X)) as [] eqn:E.
  - apply in_inb in E. exfalso. apply H. apply E.
  - reflexivity.
Qed.

Lemma in_empty : forall X, X = empty <-> forall v, ~ In v X.
Proof.
  intros X. split.
  - intros H v H'. apply in_inb in H'. rewrite H in H'. simpl in H'.
    discriminate.
  - intros H. assert (H': forall v, In v X -> In v nil).
    intros v. intros HinvX. unfold not in H.
    apply H in HinvX. exfalso. apply HinvX.
    apply incl_l_nil. unfold incl. apply H'.
Qed.

Lemma empty_intersect_retract :
  forall X Y Z, intersect X Y = empty -> incl Z Y -> intersect X Z = empty.
Proof.
  intros X Y Z H Hincl. unfold incl in Hincl.
  apply in_empty. intros v Hnin. apply intersect_in in Hnin.
  destruct Hnin as [HvinX HvinZ].
  assert (HvinY : In v Y).
  { apply Hincl. apply HvinZ. }
  assert (Hvincap : In v (intersect X Y)).
  { apply intersect_in. split. apply HvinX. apply HvinY. }
  rewrite H in Hvincap. apply Hvincap.
Qed.

Lemma gt_list_max_not_in : forall n l, list_max l < n -> ~ (In n l).
Proof.
  intros n l H Hin. destruct l as [|h t].
  - unfold In in Hin. apply Hin.
  - apply list_max_lt in H.
    assert (H2 : forall k, In k (h :: t) -> k < n).
    { apply Forall_forall. apply H. }
    apply H2 in Hin. apply Nat.lt_irrefl in Hin. apply Hin.
    intros H2. discriminate.
Qed.
    
Inductive lterm : Set :=
| Var (v : var)
| Abs (v : var) (M : lterm)
| App (M : lterm) (N : lterm).

Fixpoint freevars (M : lterm) : varset :=
  match M with
  | Var v => singleton v
  | Abs v M => remove v (freevars M)
  | App M N => union (freevars M) (freevars N)
  end.

Fixpoint boundvars (M : lterm) : varset :=
  match M with
  | Var v => empty
  | Abs v P => union (singleton v) (boundvars P)
  | App P Q => union (boundvars P) (boundvars Q)
  end.

Definition freshvar (X : varset) : var := 1 + list_max X.

Lemma freshvar_notin : forall X, ~ (In (freshvar X) X).
Proof.
  intros X. apply gt_list_max_not_in. unfold freshvar. simpl.
  apply Nat.lt_succ_diag_r.
Qed.

Fixpoint rename (M: lterm) (x : var) (y : var) :=
  match M with
  | Var v => if v =? x
             then Var y
             else Var v
  | App P Q => App (rename P x y) (rename Q x y)
  | Abs v P => if v =? x
               then Abs v P
               else Abs v (rename P x y)
  end.

Example rename_test :
  rename (App (Abs 0 (Var 0)) (Var 0)) 0 1 = App (Abs 0 (Var 0)) (Var 1).
Proof. reflexivity. Qed.

Lemma notin_abs : forall x v P,
    In x (remove v (freevars P))
    <-> x <> v /\ In x (freevars P).
Proof.
  intros x v P. split.
  - intros H. split.
    + intros H1. rewrite H1 in H. apply in_inb in H.
      rewrite notin_remove in H. discriminate H.
    + apply in_remove in H as [H2 _]. apply H2.
  - intros [H1 H2]. apply in_in_remove. apply H1. apply H2.
Qed.

Lemma rename_notin_fv :
  forall x y M, ~ (In x (freevars M)) -> rename M x y = M.
Proof.
  intros x y. induction M as [v|v P IHP|P IHP Q IHQ].
  - intros H. unfold not in H. simpl. destruct (v =? x) as [] eqn:E.
    * exfalso. apply Nat.eqb_eq in E. rewrite E in H.
      apply H. simpl. auto.
    * reflexivity.
  - simpl. intros H. destruct (v =? x) as [] eqn:E.
    + reflexivity. 
    + assert (H1: ~ In x (freevars P)).
      { intros H2. apply H. apply notin_abs. split.
        * apply Nat.eqb_neq in E. auto.
        * apply H2. }
      apply IHP in H1. rewrite H1. reflexivity.
  - simpl. unfold union. intros H.
    assert (HnInP : ~ In x (freevars P)).
    { intros H1. unfold not in H. apply H.
      apply in_or_app. left. apply H1. }
    assert (HnInQ : ~ In x (freevars Q)).
    { intros H1. unfold not in H. apply H.
      apply in_or_app. right. apply H1. }
    apply IHP in HnInP. apply IHQ in HnInQ.
    rewrite HnInP. rewrite HnInQ. reflexivity.
Qed.

Fixpoint depth (M : lterm) : nat :=
  match M with
  | Var v => 1
  | Abs v P => 1 + depth P
  | App P Q => 1 + Nat.max (depth P) (depth Q)
  end.

Lemma rename_depth : forall M x y, depth M = depth (rename M x y).
Proof.
  induction M as [v|v P IHP| P IHP Q IHQ].
  - intros x y. simpl. destruct (v =? x) as []. reflexivity. reflexivity.
  - intros x y. simpl. destruct (v =? x) as [] eqn:E.
    * simpl. reflexivity.
    * simpl. rewrite (IHP x y). reflexivity.
  - intros x y. simpl. rewrite (IHP x y). rewrite (IHQ x y). auto.
Qed. 


Fixpoint subst_t (t : nat) (M: lterm) (x : var) (N : lterm) : lterm :=
  match t with
  | 0 => M
  | S t' =>
  match M with
  | Var v   => if v =? x
               then N
               else Var v
  | App P Q => App (subst_t t' P x N) (subst_t t' Q x N)
  | Abs v P => let fvsN := freevars N in
               let fvsP := freevars P in                         
               match inb v fvsN, inb x fvsP with
               | true, true   => let fresh := freshvar (union fvsN fvsP) in
                                 (Abs fresh (subst_t t' (rename P v fresh) fresh N))
               | true, false
               | false, true  => Abs v (subst_t t' P x N)
               | false, false => Abs v P
               end
  end
  end.

Definition subst (M : lterm) (x : var) (N : lterm) : lterm :=
  subst_t (depth M) M x N.

Fixpoint subst_opt (M: lterm) (x : var) (N : lterm) : option lterm :=
  match M with
  | Var v => if v =? x
             then Some N
             else Some (Var x)
  | Abs v P => let fvsN := freevars N in
               let fvsP := freevars P in
               match inb v fvsN, inb x fvsP with
               | true, true => None
               | true, false
               | false, true => match subst_opt P x N with
                                | Some P' => Some (Abs v P')
                                | None => None
                                end
               | false, false => Some (Abs v P)
               end
  | App P Q => match subst_opt P x N, subst_opt Q x N with
               | Some P', Some Q' => Some (App P' Q')
               | _, _ => None
               end
  end.

Lemma subst_opt_bv :
  forall x M N, intersect (freevars N) (boundvars M) = empty
                -> (exists P, subst_opt M x N = Some P).
Proof.
  intros x M N. induction M as [|v P IHP|P IHP Q IHQ].
  - intros H. destruct (v =? x) as [] eqn:E.
    + simpl. rewrite E. exists N. auto.
    + simpl. rewrite E. exists (Var x). auto.
  - intros H.
    assert (H1: intersect (freevars N) (boundvars P) = empty).
    { apply (empty_intersect_retract _ (boundvars (Abs v P))).
      apply H. simpl. unfold incl. intros a HainbvP. simpl.
      right. apply HainbvP. }
    apply IHP in H1. destruct H1 as [P0 HP0]. simpl.
    destruct (inb v (freevars N)) as [] eqn:E1.
    + exfalso. apply in_inb in E1.
      assert (H1 : In v (boundvars (Abs v P))).
      { simpl. left. auto. }
      assert (H2 : In v (intersect (freevars N) (boundvars (Abs v P)))).
      { apply intersect_in. split. apply E1. apply H1. }
      rewrite H in H2. simpl in H2. apply H2.
    + destruct (inb x (freevars P)) as [] eqn:E.
      * rewrite HP0. exists (Abs v P0). auto.
      *  exists (Abs v P). auto.
  - intros H.
    assert (H1 : intersect (freevars N) (boundvars P) = empty).
    { apply (empty_intersect_retract _ (boundvars (App P Q))).
      apply H. simpl. unfold incl. intros a HainbvP.
      apply union_in. left. apply HainbvP. }
    assert (H2 : intersect (freevars N) (boundvars Q) = empty).
    { apply (empty_intersect_retract _ (boundvars (App P Q))).
      apply H. simpl. unfold incl. intros a HainbvQ.
      apply union_in. right. apply HainbvQ. }
    apply IHP in H1. apply IHQ in H2.
    destruct H1 as [P' HP']. destruct H2 as [Q' HQ'].
    simpl. rewrite HP'. rewrite HQ'. exists (App P' Q'). auto.
Qed.
