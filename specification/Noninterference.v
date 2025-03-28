From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import Dynamics.
Require Import Statics.

Section Noninterference.
  Variable (L : Lattice).

  Definition context : Type := list (string *  (L.(carrier))).

Inductive type_rel : L.(carrier) -> L.(carrier) -> nat -> nat -> Prop :=
  | TR_Low : forall o t v, 
      type_rel o t v v 
  | TR_High : forall o t v1 v2,
      L.(le) t o = false -> 
      type_rel o t v1 v2.

Definition subst_rel (o : L.(carrier)) : context -> smap -> smap -> Prop :=
  fun G g1 g2 =>
    forall (x : string),
      match lookup G x, lookup g1 x, lookup g2 x with
        | None, _, _ => True
        | Some t, Some v1, Some v2 => 
            type_rel o t v1 v2
        | Some t, _, _ => False end.
            
Definition has_sem_type (o : L.(carrier)) : context -> tm -> L.(carrier) -> Prop  :=
  fun Gamma e t =>
    forall g1 g2 v1 v2,
      subst_rel o Gamma g1 g2 ->
      big_eval (subst_many g1 e) v1 ->
      big_eval (subst_many g2 e) v2 ->
      type_rel o t v1 v2.

Lemma subst_rel_update:
  forall (o t : L.(carrier)) (Gamma : context) (g1 g2 : smap) (x : string) (v1 v2 : nat),
    type_rel o t v1 v2 ->
    subst_rel o Gamma g1 g2 ->
    subst_rel o (update Gamma x t)
      (update g1 x v1)
      (update g2 x v2).
  intros.
  unfold subst_rel.
  intro. 
  unfold update. 
  simpl. 
  destruct (x0 =? x)%string eqn:H_string.
  {
    apply H. 
  }
  {
    unfold subst_rel in H0.
    apply H0.
  }  
Qed.

Definition filter_smap (g : smap) (x : string) : smap :=
  filter (fun y => negb (String.eqb (fst y) x)) g.
    
Lemma lookup_filter:
  forall (g : smap) (x1 x2 : string),
  (x1 =? x2)%string = false
  -> lookup(filter_smap g x2) x1 = lookup g x1.
Proof.
intros.
induction g.
{
  auto.
}
{
  simpl.
  destruct a.
  simpl.
  destruct (s =? x2)%string eqn:H_x2.
  {
    
    destruct (x1 =? x2)%string eqn:H_x1.
    {
      discriminate. 
    }
    {
      simpl.
      apply String.eqb_eq in H_x2. 
      subst s.
      rewrite H_x1.
      apply IHg. 
    }
  }
  {
    simpl. destruct (x1 =? s)%string eqn:H_x1.
    {
     auto. 
    }
    {
      apply IHg. 
    } 
  }
}
Qed.

Lemma subst_rel_after_update:
  forall (Gamma : context) (g1 g2 : smap) (x : string) (v1 v2 : nat) (o t : L.(carrier)),
    type_rel o t v1 v2 ->
    subst_rel o Gamma g1 g2 ->
    subst_rel o (update Gamma x t)
      (update (filter_smap g1 x) x v1)
      (update (filter_smap g2 x) x v2).
  intros.
  intro.
  unfold update.
  simpl.
  destruct (x0 =? x)%string eqn:h.
  auto.
  destruct (lookup Gamma x0) eqn:h'; auto;
  destruct (lookup (filter_smap g1 x) x0) eqn:h'';
  destruct (lookup (filter_smap g2 x) x0) eqn:h''';
  specialize(H0 x0);
  rewrite h' in H0;
  unfold subst_rel in H0;
  pose proof (lookup_filter g1 x0 x) as h_f1;
  pose proof (lookup_filter g2 x0 x) as h_f2;
  unfold subst_rel in H0;
  rewrite h in h_f1; rewrite h in h_f2;
  specialize (h_f1 eq_refl);
  specialize (h_f2 eq_refl);
  rewrite h_f1 in h'';
  rewrite h_f2 in h''';
  rewrite h'' in H0;
  try apply H0.
  {  
    rewrite h''' in H0.
    apply H0.
  }
  {
    rewrite h''' in H0.
    apply H0.
  }
Qed.

Theorem noninterference (o t : L.(carrier)) (G : context) (e: tm) :
  has_type L G e t ->
  has_sem_type o G e t.
  intros h.
  induction h.
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 Hv1 Hv2.
    specialize (h1 x).
    destruct (lookup g1 x) eqn:E1; [ | (rewrite H in h1; contradiction) ].
    destruct (lookup g2 x) eqn:E2; [ | (rewrite H in h1; contradiction) ].
    rewrite (subst_many_var g1 x) in Hv1; rewrite E1 in Hv1; simpl in Hv1.
    rewrite (subst_many_var g2 x) in Hv2; rewrite E2 in Hv2; simpl in Hv2.
    inversion Hv1; subst.
    inversion Hv2; subst.
    rewrite H in h1.
    exact h1.    
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 h2 h3.
    rewrite subst_many_val in h2.
    rewrite subst_many_val in h3.
    inversion h2; subst.
    inversion h3; subst.
    apply TR_Low.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 h2 h3.
    rewrite subst_many_un in h2.
    rewrite subst_many_un in h3.
    inversion h2; subst.
    inversion h3; subst.

    destruct (IHh g1 g2 v v0 h1 H0 H1); subst; constructor.
    apply H.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h_sub h_eval1 h_eval2.
    rewrite subst_many_tm_bin in h_eval1.
    rewrite subst_many_tm_bin in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.

    destruct (IHh1 g1 g2 v0 v1 h_sub H1 H3); subst.
    destruct (IHh2 g1 g2 v3 v4 h_sub H2 H4); subst.
    - simpl.
      constructor.
    - simpl.
      constructor. destruct t; destruct t0; try apply H; unfold max; destruct o; auto.
    -simpl.
     constructor. destruct t; destruct t2; try apply H; unfold max; destruct o; try auto.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h_sub h_eval1 h_eval2.
    rewrite subst_many_let in h_eval1.
    rewrite subst_many_let in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.

    unfold has_sem_type in IHh2.
    specialize (IHh2 (update (filter (fun y => negb (String.eqb (fst y) x)) g1) x v0) (update (filter (fun y => negb (String.eqb (fst y) x)) g2) x v3) v1 v2).  
            
    (* want to generalize following assertions as lemmas over
       arbitrary gammas without x *)        
    assert (H_pull_out_inner_subst : forall x v s n e g,
               x <> s ->
               (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst s n (subst x v e)))
               = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst s n e)))). {
      intros.
      induction g; simpl.
      - apply (subst_neq_id_commute x0 s v n e).
        exact H.
      - destruct a; simpl; destruct (String.eqb s0 x0) eqn:H_s0_x0; simpl.
        + apply IHg.
        + rewrite (subst_neq_id_commute x0 s v n e).
          rewrite (subst_neq_id_commute x0 s0 v n0 (subst s n e)).
          apply (subst_many_subst_commute x0 v g (subst s0 n0 (subst s n e))).
          apply String.eqb_neq in H_s0_x0.
          apply id_neq_sym in H_s0_x0; exact H_s0_x0.
          exact H.
    }
    
    assert (H_update_subst_equiv : forall g v e,
               (subst_many (update (filter (fun y => negb (String.eqb (fst y) x)) g) x v) e)
               = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) e))). {
      simpl.
      induction g; simpl.
      - reflexivity.
      - destruct a; simpl.
        destruct (negb (String.eqb s x)) eqn:H_eq; simpl.
        + apply Bool.negb_true_iff in H_eq; apply String.eqb_neq in H_eq.
          intros v e; specialize (H_pull_out_inner_subst x v s n e g); auto.
        + apply IHg.
    }
    
    rewrite (H_update_subst_equiv g1 v0 e2) in IHh2.
    rewrite (H_update_subst_equiv g2 v3 e2) in IHh2.
    
    unfold has_sem_type in IHh1.
    apply IHh2.
    apply subst_rel_after_update.
    eapply IHh1.
    apply h_sub.
    apply H3.
    apply H5.
    apply h_sub.
    apply H4.
    apply H6.
    }
Qed.