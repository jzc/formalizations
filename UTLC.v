From mathcomp Require Import all_ssreflect finmap.

Definition var := nat.

Inductive lterm : Set :=
| Var (x : var)
| App (M : lterm) (N : lterm)
| Abs (x : var) (M : lterm).

Fixpoint eq_lterm (M N : lterm) : bool :=
  match M, N with
  | Var x, Var y => x == y
  | App P Q, App P' Q' => (eq_lterm P P') && (eq_lterm Q Q')
  | Abs x P, Abs y P' => (x == y) && (eq_lterm P P')
  | _, _ => false
  end.

Lemma eq_ltermP : Equality.axiom eq_lterm.
Proof.
  rewrite /Equality.axiom.
  elim=> [x|M IHM N IHN|x M IHM] [y|M' N'|y M'] /=.
  - case: (x==y) /eqP.
    + move=> Heq. constructor. by apply: f_equal.
    + move=> Hneq. constructor. move=> Heq. by injection Heq.
  - constructor. by [].
  - constructor. by [].
  - constructor. by [].
  - have: reflect (M = M') (eq_lterm M M') by [].
    have: reflect (N = N') (eq_lterm N N') by [].
    elim=> [eqNT | eqNF] [eqMT | eqMF] /=.
    + constructor. by apply: f_equal2.
    + constructor. move=> Heq. by injection Heq.
    + constructor. move=> Heq. by injection Heq.
    + constructor. move=> Heq. by injection Heq.
  - constructor. by [].
  - constructor. by [].
  - constructor. by [].
  - have: reflect (M = M') (eq_lterm M M') by [].
    elim=> [eqMT | eqMF];
    case: (x == y) /eqP => Heqxy /=.
    + constructor. by apply: f_equal2.
    + constructor. move=> Heq. by injection Heq.
    + constructor. move=> Heq. by injection Heq.
    + constructor. move=> Heq. by injection Heq.
Qed.

Definition lterm_eqMixin := Equality.Mixin eq_ltermP.
Canonical lterm_eqType := @Equality.Pack lterm lterm_eqMixin.
                                
Definition varset := {fset var}. 
(* Definition singleton (x : var) := [:: x]. *)
(* Definition remove (x : var) (S : varset) : varset := *)
  (* filter (fun y => x != y) S. *)

(* Lemma in_remove : forall x S, x \notin (remove x S). *)
(* Proof. *)
(*   move=> x S. *)
(*   rewrite /remove. apply/negP.  *)
(*   rewrite mem_filter. *)
(*   move/andP => [Heq _]. *)
(*   by move/eqP: Heq => Heq. *)
(* Qed. *)

Open Scope fset_scope.

Fixpoint freevars (M : lterm) : varset :=
  match M with
  | Var x => [fset x]
  | App P Q => (freevars P `|` freevars Q)
  | Abs x P => (freevars P `\ x)
  end.

Fixpoint boundvars (M : lterm) : varset :=
  match M with
  | Var x => fset0
  | App P Q => (boundvars P `|` boundvars Q)
  | Abs x P => x |` boundvars P
  end.

Fixpoint subst (x : var) (N M : lterm) :=
  match M with
  | Var y => if x == y
             then N
             else Var y
  | App P Q => App (subst x N P) (subst x N Q)
  | Abs y P => if x == y
               then Abs y P
               else Abs y (subst x N P)
  end.

Lemma subst_notin_fv (x : var) N M : 
  x \notin freevars M -> M = subst x N M.
Proof.
  elim: M => [y|P IHP Q IHQ|y P IHP].
  - rewrite inE /=. move/negbTE=> H. by rewrite H.
  - rewrite inE -/freevars negb_or.    
    move/andP=> [HnP HnQ].
      by rewrite {1}(IHP HnP) {1}(IHQ HnQ).
  - rewrite inE -/freevars. case E: (x == y).
    + by rewrite /= E.
    + rewrite /= E.
      rewrite negb_and -implybE.
      rewrite inE. move/negbT: E => E.
      move/implyP=> H.
        by rewrite {1}(IHP (H E)).
Qed.

Lemma freevars_subset_app : forall M N, freevars M `<=` freevars (App M N).
Proof.
  move=> M N. rewrite /=. by apply: fsubsetUl.
Qed.

Definition variable_convention (M : lterm) :=
  [disjoint (freevars M) & (boundvars M)].

Lemma freevars_subst : forall x N M,
    freevars (subst x N M) `<=` freevars M `\ x `|` freevars N.
Proof.
  move=> x N. elim.
  - move=> y /=.
    apply/fsubsetP. rewrite /sub_mem. 
    move=> z Hz. apply/fsetUP. move: Hz. case E: (x==y).
    + by right.
    + rewrite /= {1}inE. move=> Hz. left. rewrite in_fsetD1.
      apply/andP. split.
      * rewrite eq_sym. move/eqP: Hz => Hz.
        rewrite Hz. by apply: negbT.
      * by rewrite inE.
  - move=> P /fsubsetP IHP Q /fsubsetP IHQ /=.    
    apply/fsubsetP.
    move: IHP IHQ. rewrite /sub_mem. move=> IHP IHQ.
    move=> /= z. move/fsetUP=> H.
    apply/fsetUP.
    have: z \in (freevars P `\x `|` freevars N)
                \/ z \in (freevars Q `\x `|` freevars N).
    case: H. by left; apply IHP. by right; apply IHQ.
    move=> [/fsetUP [/fsetD1P H11|H12]| /fsetUP [/fsetD1P H21|H22]].
    + left. apply/fsetD1P. split. by tauto. by apply/fsetUP; tauto.
    + by tauto.
    + left. apply/fsetD1P. split. by tauto. by apply/fsetUP; tauto.
    + by tauto.
  - move=> y P /fsubsetP IHP. apply/fsubsetP.
    move: IHP. rewrite /sub_mem. move=> IHP.
    move=> z /=. case E: (x == y).
    + move/eqP: E => E /=. rewrite E.
      move/fsetD1P=> [Hzy HzP].      
      apply/fsetUP. left.
      apply/fsetD1P. split. by []. 
      apply/fsetD1P. by [].
    + rewrite /=.
      move/fsetD1P=> [Hzy HzP].
      move/IHP/fsetUP: HzP => [HzP1|HzP2].
      * apply/fsetUP. left.
        apply/fsetD1P.
        move/fsetD1P: HzP1 => [HzP11 HzP12].
        split. by []. apply/fsetD1P. by [].
      * by apply/fsetUP; tauto.
Qed.

Lemma boundvars_subst : 

Check variable_convention.

Lemma disjointABCD_BD {K : choiceType} : forall (A B C D : {fset K}),
    [disjoint A `|` B & C `|` D] -> [disjoint B & D].
Proof.
  move=> A B C D. 
  rewrite fdisjointUX.
  move/andP => [_ H]. move: H.
  rewrite fdisjointXU.
    by move/andP => [_ H].
Qed.  

Lemma variable_convention_appl : forall P Q,
    variable_convention (App P Q) -> variable_convention Q.
Proof.
  move=> P Q. rewrite /variable_convention /=.
    by apply disjointABCD_BD.
Qed.

(* Lemma variable_convention_applr : forall P Q, *)
    (* variable_convention P -> variable_convention Q -> *)
    (* variable_convention (App P Q). *)
(* Proof. *)
  (* move=> P Q. rewrite /variable_convention /=. HP HQ.  *)

Lemma variable_convention_stable : forall x N M,
    variable_convention (App (Abs x M) N) -> variable_convention (subst x N M).
Proof.
  move=> x N. case.
  - rewrite /=. move=> y H.
    have: variable_convention N. by apply: (variable_convention_appl (Abs x (Var y))).
    case E: (x == y).
    + by [].
    + move=> _. rewrite /variable_convention /freevars /boundvars.
        by apply: fdisjointX0.
  - rewrite /variable_convention /=.
    move=> P Q /fdisjointP H /=. apply/fdisjointP. move=> z.
    move/fsetUP=> HzP.
    suffices {HzP}: z \in (freevars P `|` freevars Q) `\ x `|` freevars N.
    move/H=> H'.
    
    
    + rewrite in_fsetU negb_or. apply/andP. split.
      have: z \in freevars P `\ x `|` freevars N.
      { move/fsubsetP: (freevars_subst x N P).
      rewrite /sub_mem. move=> Hss. by apply Hss. }
      move=> HzP'.
        
      
      move: HzP. move/freevars_subst.


Section beta.
  Inductive beta1 : lterm -> lterm -> Prop :=
  | beta1_redex
    : forall x M N, beta1 (App (Abs x M) N) (subst x N M)
  | beta1_appl
    : forall P P' Q, beta1 P P' -> beta1 (App P Q) (App P' Q)
  | beta1_appr
    : forall P Q Q', beta1 Q Q' -> beta1 (App P Q) (App P Q')
  | beta1_abs
    : forall x P P', beta1 P P' -> beta1 (Abs x P) (Abs x P').

  Inductive beta : lterm -> lterm -> Prop :=
  | beta_refl
    : forall M, beta M M
  | beta_step
    : forall P Q R, beta P Q -> beta1 Q R -> beta P R.

  Notation "M -->b N" := (beta1 M N) (at level 70, no associativity).
  Notation "M -->b* N" := (beta M N) (at level 70, no associativity).

  Lemma beta1_beta : forall M N, M -->b N -> M -->b* N.
  Proof.
    move=> M N H.
    apply: (beta_step M M N).
    - by constructor.
    - by [].
  Qed.

  Lemma beta_left : forall P Q R, P -->b Q -> Q -->b* R -> P -->b* R.
  Proof.
    move=> P Q R H1 H2. move: H2 H1. elim.
    - by apply: beta1_beta.
    - move=> P' Q' R' H1 H2 H3 H4.
      apply: (beta_step _ Q').
      + by apply: H2.
      + by [].
  Qed. 

  Lemma beta_transitive : forall P Q R,
      P -->b* Q -> Q -->b* R ->
      P -->b* R.
  Proof.
    move=> P Q R. elim.
    - by [].
    - move=> P' Q' R' H1 H2 H3 H4.
      apply: H2. by apply: (beta_left _ R').
  Qed.

  Lemma beta_stable_appl :
    forall M M' N, M -->b* M' -> App M N -->b* App M' N.
  Proof.
    move=> M M' N. elim=> [P|P Q R IH].
    - by constructor.
    - move=> H1 H2.
      have: App Q N -->b App R N by constructor.
        by apply: (beta_step _ (App Q N) _).
  Qed.

  Lemma beta_stable_appr :
    forall M N N', N -->b* N' -> App M N -->b* App M N'.
  Proof.
    move=> M N N'. elim=> [P|P Q R IH].
    - by constructor.
    - move=> H1 H2.
      have: App M Q -->b App M R by constructor.
        by apply: (beta_step _ (App M Q) _).
  Qed.

  Lemma beta_stable_abs :
    forall x M M', M -->b* M' -> Abs x M -->b* Abs x M'.
  Proof.
    move=> x M M'. elim=> [P| P Q R IH].
    - by constructor.
    - move=> H1 H2.
      have: Abs x Q -->b Abs x R by constructor.
        by apply: (beta_step _ (Abs x Q) _ ).
  Qed.

  Lemma beta_stable_subst1 :
    forall x M N N', N -->b N' -> subst x N M -->b* subst x N' M.
  Proof.
    move=> x M N N' HN. elim: M => [y|P IHP Q IHQ|y P IHP] /=.
    - case: (x == y).
      + by apply: beta1_beta.
      + by constructor.
    - have:
        App (subst x N P) (subst x N Q)
            -->b* App (subst x N' P) (subst x N Q)
        by apply: beta_stable_appl.
      move=> H1.
      have:
        App (subst x N' P) (subst x N Q)
            -->b* App (subst x N' P) (subst x N' Q)
        by apply: beta_stable_appr.
      move=> H2.
        by apply: (beta_transitive _ _ _ H1 H2).
    - case: (x == y).
      + by constructor.
      + by apply: beta_stable_abs.
  Qed.  

  Lemma subst_comm : forall (x y : var) P Q N,
      x != y -> y \notin freevars N ->
      subst x N (subst y Q P) = subst y (subst x N Q) (subst x N P).
  Proof.
    move=> x y P Q N Hneq Hfvs.
    elim: P => [z|P' IHP' Q' IHQ'|z P IHP'].
    - rewrite /=. case E: (y == z).
      + move/eqP: E => E. rewrite <- E.
        move/negbTE: Hneq => Hneq.
        by rewrite Hneq /= eq_refl.
      + case E': (x == z).
        * rewrite /= E'.
            by apply subst_notin_fv.
        * by rewrite /= E E'.
    - by rewrite /= IHP' IHQ'.
    - rewrite /=. case E1: (y==z); case E2: (x==z); rewrite /= E1 E2.
      - by [].
      - by [].
      - 
 
      
  Lemma beta_stable_subst2 : 
    forall x M M' N, M -->b M' -> subst x N M -->b* subst x N M'.
  Proof.
    move=> x M M' N. elim: M => [y| P IHP Q IHQ|y P IHP] /=.
  Admitted.

  Lemma redex_inv :
    forall x M N Q, App (Abs x M) N -->b Q ->
                    (exists M', App (Abs x M) N -->b App (Abs x M') N)
                    \/ (exists N', App (Abs x M) N -->b App (Abs x M) N').
  Proof.
    move=> x M N Q. case: Q.
    

  Lemma diamond :
    forall P Q Q', P -->b Q -> P -->b Q' -> exists R, Q -->b* R /\ Q' -->b* R.
  Proof.
    move=> P Q Q' H1 H2. move: Q' H2. elim H1.
    + move=> x M N Q'.
    

(* Definition index := seq nat. *)

(* Fixpoint is_valid_index (M : lterm) (idx : index) : bool := *)
(*   match idx with *)
(*   | [::] => true  *)
(*   | i :: idx' => match M with *)
(*                | Var x => false *)
(*                | Abs x P => match i with *)
(*                            | 0 => is_valid_index P idx' *)
(*                            | _ => false *)
(*                            end *)
(*                | App P Q => match i with *)
(*                            | 0 => is_valid_index P idx' *)
(*                            | 1 => is_valid_index Q idx' *)
(*                            | _ => false *)
(*                            end *)
(*                end *)
(*   end. *)

(* Fixpoint foo (n m : nat) := *)
(*   match m with *)
(*   | 0 => true *)
(*   | S k => false && foo m k *)
(*   end. *)

(* Variable x : nat. *)
(* Compute (foo x 0). *)

(* Fixpoint bar n m := *)
(*   match m with *)
(*   | 0 => n *)
(*   | S k => m *)
(*   end. *)

(* Compute bar n 0. *)



(* Lemma bar : forall n, reflect True (foo n 0). *)
(* Proof. *)
(*   move=> n /=. simpl. *)



(* Inductive valid_index : lterm -> index -> Prop := *)
(* | valid_nil *)
(*   : forall M, valid_index M nil *)
(* | valid_abs *)
(*   : forall x M idxM, valid_index M idxM -> valid_index (Abs x M) (0 :: idxM) *)
(* | valid_appl *)
(*   : forall M N idxM, valid_index M idxM -> valid_index (App M N) (0 :: idxM) *)
(* | valid_appr *)
(*   : forall M N idxN, valid_index N idxN -> valid_index (App M N) (1 :: idxN). *)

(* Lemma valid_indexP : forall M idx, reflect (valid_index M idx) (is_valid_index M idx). *)
(* Proof. *)
(*   move=> M idx. *)
(*   elim: idx. *)
(*   - cbv. *)

(*     case: M => [x|P Q|x P] /=; by constructor; constructor. *)
(*   - move=> i idx'. case: M => [x|P Q|x P] /=. *)
(*     + move=> IH. constructor. move=> Hv. elim E: Hv. *)
      
    
(* Fixpoint get_opt (M : lterm) (idx : index) : option lterm := *)
(*   match idx with *)
(*   | nil => M *)
(*   | i :: idx' => match M with *)
(*                |  *)
  
(*   match M, idx with *)
(*   | _, nil => Some M *)
(*   | Abs x P, i :: idx' => match h with *)
(*                      | 0 => get_opt P t *)
(*                      | _ => None *)
(*                      end *)
(*   | App P Q, i :: idx => match h with *)
(*                      | 0 => get_opt P t *)
(*                      | 1 => get_opt Q t *)
(*                      | _ => None *)
(*                      end *)
(*   | _, _ => None *)
(*   end. *)

(* Fixpoint replace_index (M : lterm) (idx : index) (N : lterm) : lterm := *)
(*   match idx with *)
(*   | nil => N *)
(*   | i :: idx' *)

(* Fixpoint i {M} (idxM : index M) (N : lterm) : option (index N) := *)
(*   match idxM, N with *)
(*   | index_root _, _ => Some (index_root _) *)
(*   | _, _ => None *)
(*   end. *)

(* Inductive isomorphic_index : forall M N, index M -> index N -> Prop := *)
(* | . *)


(* Check (index_abs 1 _ (index_root (Abs 0 (Var 0)))). *)

Section subst_op.
  Variable subst : var -> lterm -> lterm.
  Variable freevars : lterm -> varset.

  

                                             

Fixpoint subst (x : var) (N M : lterm) :=
  match M with
  | Var y => if x == y
            then N
            else Var y
  | App P Q => App (subst x N P) (subst x N Q)
  | Abs y P => if x == y
              then Abs y P
              else Abs y (subst x N P)
  end.

Fixpoint ca_subst (x : var) (N M : lterm) : option lterm :=
  match M with
  | Var y => if x == y
            then Some N
            else Some (Var y)
  | App P Q => match ca_subst x N P, ca_subst x N Q with
              | Some P', Some Q' => Some (App P' Q')
              | _, _ => None
              end
  | Abs y P => if x == y
              then Some (Abs y P)
              else if y \in (freevars N)
                   then None
                   else match ca_subst x N P with
                        | Some P' => Some (Abs y P')
                        | _ => None
                        end
  end.

Fixpoint shift_f (f: nat -> nat) (d : nat) (M : lterm) : lterm :=
  match M with
  | Var x => if (PeanoNat.Nat.leb d x)
            then Var (f x)
            else Var x
  | App P Q => App (shift_f f d P) (shift_f f d Q)
  | Abs x P => Abs x (shift_f f (S d) P)
  end.

Definition shift_up := shift_f S 0.
Definition shift_down := shift_f pred 0.
  
Fixpoint db_subst (x : var) (N M : lterm) : lterm :=
  match M with
  | Var y => if var_eq_dec x y
            then N
            else Var y
  | App P Q => App (db_subst x N P) (db_subst x N Q)
  | Abs y P => Abs y (db_subst (S x) (shift_up N) P)
  end.

Definition db_subst_redex (x : var) (M N : lterm) :=
  shift_down (db_subst x (shift_up N) M).

Inductive db_beta_reducible : lterm -> lterm -> Prop :=
| dbbr_redex (x : var) (M N : lterm)
  : db_beta_reducible (App (Abs x M) N)
                      (db_subst_redex x N M)
| dbbr_appl (M M' N : lterm)
            (HM : db_beta_reducible M M')
  : db_beta_reducible (App M N) (App M' N) 
| dbbr_appr (M N N' : lterm)
            (HN : db_beta_reducible N N')
  : db_beta_reducible (App M N) (App M N')
| dbbr_abs (x : var) (M M' : lterm)
           (HM : db_beta_reducible M M')
  : db_beta_reducible (Abs x M) (Abs x M').

Inductive redex : lterm -> Prop :=
| redex_intro (x : var) (M N : lterm)
  : redex (App (Abs x M) N).

Inductive immd_subterm : lterm -> lterm -> Prop :=
| immd_subterm_appl (M N : lterm) : immd_subterm M (App M N)
| immd_subterm_appr (M N : lterm) : immd_subterm N (App M N)
| immd_subterm_abs (x : var) (M : lterm) : immd_subterm M (Abs x M).

Inductive nf : lterm -> Prop :=
| nf_var (x : var) : nf (Var x)
| nf_app_var (x : var) (N : lterm) (HN : nf N)
  : nf (App (Var x) N)
| nf_app_app (P Q N : lterm) (HPQ : nf (App P Q))
             (HN : nf N)
  : nf (App (App P Q) N)
| nf_abs (x : var) (M : lterm) (HM : nf M)
  : nf (Abs x M).    

Lemma nf_dec : forall M, {nf M} + {~ nf M}.
Proof.
  intros M. induction M.
  - left. apply nf_var.
  - destruct M1; destruct IHM2.
    + left. apply nf_app_var. apply n.
    + apply right. intros H. inversion H. contradiction.
    + destruct IHM1. left. apply nf_app_app. apply n0. apply n.
      right. intros H. inversion H. contradiction.
    + right. intros H. inversion H. contradiction.
    + right. intros H. inversion H.
    + right. intros H. inversion H.
  - destruct IHM. left. apply nf_abs. apply n.
    right. intros H. inversion H. contradiction.
Qed.

Lemma not_nf : forall M,
    ~ nf M
    -> redex M
      \/ (exists M', immd_subterm M' M /\ ~ nf M').
Proof.
  intros M Hnnf. destruct M as [].
  - exfalso. apply Hnnf. apply nf_var.
  - destruct M1 as [].
    + assert (Hnnfm2 : ~ nf M2).
      { intros Hnfm2. apply Hnnf.
        apply nf_app_var. apply Hnfm2. }
      right. exists M2. split. apply immd_subterm_appr.
      apply Hnnfm2.
    + destruct (nf_dec M2).
      * assert (Hnnfapp : ~ nf (App M1_1 M1_2)).
        { intros Hnfapp. apply Hnnf. apply nf_app_app.
          auto. auto. }
        right. exists (App M1_1 M1_2). split.
        apply immd_subterm_appl. auto.
      * right. exists M2. split. apply immd_subterm_appr.
        auto.
    + left. apply redex_intro.
  - right. assert (HnnfM : ~ nf M).
    { intros HnfM. apply Hnnf. apply nf_abs. auto. }
    exists M. split. apply immd_subterm_abs. auto.
Qed.
    
      
Lemma nf_not_exists : forall M, nf M -> ~ exists M', db_beta_reducible M M'.
Proof.
  intros M Hnf. induction Hnf.
  - intros [M' HM']. inversion HM'.
  - intros [M' HM']. inversion HM'.
    inversion HM. apply IHHnf. exists N'. apply HN.
  - intros [M' HM']. inversion HM'.
    apply IHHnf1. exists M'0. apply HM.
    apply IHHnf2. exists N'. apply HN.
  - intros [M' HM']. inversion HM'.
    apply IHHnf. exists M'0. apply HM.
Qed.

Lemma redex_reducible : forall M,
    redex M -> exists M', db_beta_reducible M M'.
Proof.
  intros _ [x M N]. exists (db_subst_redex x N M). 
  apply dbbr_redex.
Qed.

Lemma not_nf_exists : forall M, ~ nf M -> exists M', db_beta_reducible M M'.
Proof.
  intros M Hnnf. induction M.
  - exfalso. apply Hnnf. apply nf_var.
  - apply not_nf in Hnnf. destruct Hnnf as [Hredex|Hnredex].
    + apply redex_reducible in Hredex.
      apply Hredex.
    + destruct Hnredex as [M' [Hsub HnnfM']].
      inversion Hsub.
      * rewrite H1 in HnnfM'.
        apply IHM1 in HnnfM'.
        destruct HnnfM' as [M1' HM1'].
        exists (App M1' M2). apply dbbr_appl. auto.
      * rewrite H2 in HnnfM'.
        apply IHM2 in HnnfM'.
        destruct HnnfM' as [M2' HM2'].
        exists (App M1 M2'). apply dbbr_appr. auto.
  - apply not_nf in Hnnf. destruct Hnnf as [Hredex|Hnredex].
    + inversion Hredex.    
    + destruct Hnredex as [M' [Hsub HM']].
      inversion Hsub. rewrite H2 in HM'. apply IHM in HM'.
      destruct HM' as [M'' HM''].
      exists (Abs x M''). apply dbbr_abs. apply HM''.
Qed.

Inductive bigstep : lterm -> lterm -> Prop :=
| bigstep_nf : forall M,
    nf M
    -> bigstep M M
| bigstep_abs : forall x M M',
    bigstep M M'
    -> bigstep (Abs x M) (Abs x M')
| bigstep_abs_app : forall x M M' N P,
    bigstep M (Abs x M') -> bigstep (db_subst_redex x N M') P
    -> bigstep (App M N) P
| bigstep_var_app : forall x M N N',
    bigstep M (Var x) -> bigstep N N'
    -> bigstep (App M N) (App (Var x) N')
| bigstep_app_app : forall M P Q N N',
    bigstep M (App P Q) -> bigstep N N'
    -> bigstep (App M N) (App (App P Q) N').

Notation "M ⇓ N" := (bigstep M N) (at level 70).
Notation "M ->b N" := (db_beta_reducible M N) (at level 70).
Notation "M ->b* N" := (clos_refl_trans_1n _ db_beta_reducible M N) (at level 70).

Lemma bigstep_to_nf : forall M N, M ⇓ N -> nf                                                               N. 
Proof.
  intros M N Hstep. induction Hstep.
  - auto.
  - apply nf_abs. auto.
  - auto.
  - apply nf_app_var. auto.
  - apply nf_app_app. auto. auto.
Qed.

(* Lemma multistep_bigstep : forall M N, (M ->b* N) -> nf N -> M ⇓ N. *)
(* Proof. *)
(*   intros M N Hmultistep Hnf. induction Hmultistep. *)
(*   - apply bigstep_nf. auto. *)
(*   - apply IHHmultistep in Hnf. inversion Hnf. *)

(* Lemma bigstep_neq : forall M N, M ⇓ N -> M <> N -> ~ nf M. *)

Lemma bigstep_deterministic : forall M P Q, M ⇓ P -> M ⇓ Q -> P = Q.
Proof.
  intros M P Q HMP HMQ. induction HMP.
  - inversion HMQ. reflexivity.
  
  - intros P Q HMP HMQ. inversion HMP. inversion HMQ. reflexivity.
  - intros P Q HMP HMQ. inversion HMP.
    + inversion H.
      
Inductive db_beta_reducibleT : lterm -> lterm -> Type :=
| dbbr_redexT (x : var) (M N : lterm)
  : db_beta_reducibleT (App (Abs x M) N)
                      (db_subst_redex x N M)
| dbbr_applT (M M' N : lterm)
            (HM : db_beta_reducibleT M M')
  : db_beta_reducibleT (App M N) (App M' N)
| dbbr_apprT (M N N' : lterm)
            (HN : db_beta_reducibleT N N')
  : db_beta_reducibleT (App M N) (App M N')
| dbbr_absT (x : var) (M M' : lterm)
           (HM : db_beta_reducibleT M M')
  : db_beta_reducibleT (Abs x M) (Abs x M').

Definition derivation := { M : lterm & { N : lterm & db_beta_reducible M N} }.

Inductive isd : derivation -> derivation -> Prop :=
| isd_appl : forall M M' N (d : db_beta_reducibleT M M'),
    isd (existT 

Fixpoint depth {M N} (d : db_beta_reducibleT M N) : nat :=
  match d with
  | dbbr_redexT _ _ _ => 0
  | dbbr_applT _ _ _ d' => S (depth d')
  | dbbr_apprT _ _ _ d' => S (depth d')
  | dbbr_absT _ _ _ d' => S (depth d')
  end.

Definition derivation_prop := forall M N, db_beta_reducibleT M N -> Prop.

Definition thing (P : derivation_prop) (n : nat) :=
  forall M N (d : db_beta_reducibleT M N), depth d = n -> P M N d.

Lemma depth_induciton : forall (P : derivation_prop),
    (forall M N (dx : db_beta_reducibleT M N),
        (forall M' N' (dy : db_beta_reducibleT M' N'),
            depth dy < depth dx -> P _ _ dy)
           -> P _ _ dx)
    -> forall M N (dx : db_beta_reducibleT M N), P _ _ dx.
Proof.
  intros P Hind.
  
  assert (H : forall n, thing P n).
  { apply (well_founded_ind Nat.lt_wf_0).
    intros x Hx. unfold thing.
    intros M N d Hd. apply Hind.
    intros M' N' dy Hdy.
    assert (H2 : thing P (depth dy)).
    { apply Hx. rewrite Hd in Hdy. apply Hdy. }
    unfold thing in H2. apply H2.
    reflexivity. }
  intros M N dx. unfold thing in H. apply H
  with (n:= depth dx). reflexivity.
Qed.

Definition lex_lt (p1 p2 : nat * nat) : Prop :=
  let (px1, py1) := p1 in
  let (px2, py2) := p2 in
  px1 < px2 \/ (px1 = px2 /\ py1 < py2).

Lemma wf_lex_lt : well_founded lex_lt.
Proof.
  assert (H1 : forall y, Acc lex_lt (0, y)).
  { apply (well_founded_ind Nat.lt_wf_0).
    intros x IH. destruct x.
    - apply Acc_intro. intros [x' y'] Hp.
      simpl in Hp. destruct Hp. inversion H.
      destruct H as [_ H]. inversion H.
    - apply Acc_intro. intros [x' y'] Hp.
      simpl in Hp. destruct Hp. inversion H.
      destruct H as [Hx' Hy']. rewrite Hx'.
      apply IH. apply Hy'. }
  assert (H2 : forall y, (forall x, Acc lex_lt (x, y))).
  { apply (well_founded_ind Nat.lt_wf_0).
    intros x. intros IH.


    destruct x. intros _. apply H1.
    intros IH. apply Acc_intro.
    intros p. destruct p as [x' y'].
    
    simpl. intros Hp. destruct Hp.
    - apply IH in H.
    
  intros p. destruct p as [x y].

  
  apply (well_founded_ind Nat.lt_wf_0).
  - intros x' IH. apply (well_founded_ind Nat.lt_wf_0). Admitted.
  
  
    (* induction y. *)
    (* + apply Acc_intro. intros [x' y'] Hp'. *)
    (*   simpl in Hp'. destruct Hp' as []. *)
    (*   inversion H. destruct H as [_ H]. inversion H. *)
    (* + apply Acc_intro. intros [x' y']. simpl. intros H. *)
    (*   inversion IHy. destruct H. inversion H. *)
    (*   destruct H as [Hx' Hy']. rewrite Hx'. *)
    (*   destruct (Nat.compare y y') as [| |] eqn:E. *)
    (*   * apply Nat.compare_eq in E. rewrite <- E. *)
    (*     apply IHy. *)
    (*   * apply Nat.compare_lt_iff in E. *)
    (*     apply H0. simpl. right. Admitted. *)

Lemma wf_diag : well_founded (fun (p1 p2 : nat * nat) => let (x1, y1) := p1 in
                                                  let (x2, y2) := p2 in
                                                  x1 < x2 /\ y1 < y2).

intros p. 

                           
      
  
Definition
  immd_subderivation (sd1 sd2 : { d | exists P Q, d = db_beta_reducibleT P Q }) : Prop :=
  let (d1, Hd1) := sd1 in
  let (d2, Hd2) := sd2 in
  (exists M M' N, d2 = dbbr_applT M M' N d1).

Inductive immd_subderivation
          (d1 d2 : { d | exists P Q, d = db_beta_reducible P Q }) : Prop :=
| immd_sd_appl (H : exists M M' N, proj1_sig d2 = dbbr_applT M M' N (proj2_sig d1))
  : immd_subderivation d1 d2.

Lemma immd_subderivation_wf : forall p q r s,
    well_founded (immd_subderivation p q r s).
  
  
Lemma diamond : forall M P Q,
    db_beta_reducible M P
    -> db_beta_reducible M Q
    -> P = Q \/ exists R, db_beta_reducible P R /\ db_beta_reducible Q R.
Proof.
  intros M P Q HMP HMQ. 
