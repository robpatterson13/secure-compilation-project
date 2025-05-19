From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import Dynamics.
Require Import Statics.

Section Noninterference.
  Variable (L : Lattice).

Inductive type_rel : L.(carrier) -> L.(carrier) -> value -> value -> Prop :=
  | TR_Low : forall o t v, 
      type_rel o t v v 
  | TR_High : forall o t v1 v2,
      L.(le) t o = false -> 
      type_rel o t v1 v2.

Inductive shape_rel : tm L -> tm L -> Prop :=
  | SR_Var : forall x,
      shape_rel (tm_var L x) (tm_var L x)
  | SR_Var_Left : forall x v1,
      shape_rel (tm_var L x) (tm_val L v1)
  | SR_Var_Right : forall x v1,
      shape_rel (tm_val L v1) (tm_var L x)
  | SR_Val : forall v1 v2,
      shape_rel (tm_val L v1) (tm_val L v2)
  | SR_Un : forall e1 e2,
      shape_rel e1 e2 ->
      shape_rel (tm_un L e1) (tm_un L e2)
  | SR_Bin : forall e1 e2 e3 e4,
      shape_rel e1 e3 ->
      shape_rel e2 e4 ->
      shape_rel (tm_bin L e1 e2) (tm_bin L e3 e4)
  | SR_Let : forall e1 e2 e3 e4 x,
      shape_rel e1 e3 ->
      shape_rel e2 e4 ->
      shape_rel (tm_let L x e1 e2) (tm_let L x e3 e4)
  | SR_Declass : forall e1 e2 Label,
      shape_rel e1 e2 ->
      shape_rel (tm_declass L e1 Label) (tm_declass L e2 Label).

      
Inductive trace_rel :  L.(carrier) -> trace L -> trace L -> Prop :=
| Decl_Pub : forall (l1 l2 o: L.(carrier)) v1 v2 (tr1 tr2 : trace L),
    trace_rel o tr1 tr2 ->
    L.(le) l1 o = true \/
    L.(le) l2 o = true -> 
    v1 = v2 ->
    trace_rel o ((v1, l1)::tr1) ((v2, l2)::tr2)
| Decl_Sec : forall (l1 l2 o: L.(carrier)) v1 v2 (tr1 tr2 : trace L),
    trace_rel o tr1 tr2 ->
    L.(le) l1 o = false /\
    L.(le) l2 o = false -> 
    trace_rel o ((v1, l1)::tr1) ((v2, l2)::tr2)
| Decl_Empty : forall o tr1 tr2,
  tr1 = [] ->
  tr2 = [] ->
  trace_rel o tr1 tr2.

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

Definition subst_rel (o : L.(carrier)) : context L -> smap -> smap -> Prop :=
  fun G g1 g2 =>
    forall (x : string),
      match lookup G x, lookup g1 x, lookup g2 x with
        | None, _, _ => True 
        | Some t, Some v1, Some v2 => 
            type_rel o t v1 v2
        | Some t, _, _ => False end.

Inductive same_type : value -> type -> Prop :=
| same_nat : forall t v n,
  t = nat_type ->
  v = (VNat n) ->
  same_type v t
| same_bool : forall t v b,
  t = bool_type ->
  v = (VBool b) ->
  same_type v t.
    
Definition well_typed : smap -> type_context -> Prop :=
 fun g tG => forall x,
  match lookup tG x, lookup g x with
  | None, _ => True
  | Some t, Some v => same_type v t
  | Some t, _ => False end.

(* Inductive well_typed_exp : smap -> type_context -> tm L-> Prop :=
| WT_Var : forall g1 TGamma v1 val1 x,
  lookup TGamma x = Some val1 -> 
  lookup g1 x = Some v1 ->
  same_type v1 val1 ->
  well_typed_exp g1 TGamma (tm_var L x)
| WT_Val : forall g1 TGamma v,
  well_typed_exp g1 TGamma (tm_val L v)
| WT_Un : forall g1 TGamma e1,
  well_typed_exp g1 TGamma e1 ->
  well_typed_exp g1 TGamma (tm_un L e1)
| WT_Bin : forall g1 TGamma e1 e2,
  well_typed_exp g1 TGamma e1 ->
  well_typed_exp g1 TGamma e2 ->
  well_typed_exp g1 TGamma (tm_bin L e1 e2)
| WT_Let : forall g1 TGamma e1 e2 v tr val x,
  well_typed_exp g1 TGamma e1 ->
  big_eval L e1 v tr ->
  same_type v val ->
  well_typed_exp (update g1 x v) (update TGamma x val) e2 ->
  well_typed_exp g1 TGamma (tm_let L x e1 e2). *)


Definition has_sem_type (o : L.(carrier)) : context L -> type_context -> tm L -> L.(carrier) -> Prop  :=
  fun Gamma TGamma e t =>
    forall g1 g2 v1 v2 tr1 tr2,
      well_typed g1 TGamma ->
      well_typed g2 TGamma ->
      subst_rel o Gamma g1 g2 ->
      trace_rel o tr1 tr2 ->
      big_eval L (subst_many L g1 e) v1 tr1 ->
      big_eval L (subst_many L g2 e) v2 tr2 ->
      type_rel o t v1 v2.

Lemma subst_rel_update:
  forall (o t : L.(carrier)) (Gamma : context L) (g1 g2 : smap) (x : string) (v1 v2 : value),
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

Lemma well_typed_after_update:
  forall (Gamma : type_context) (g : smap) (x : string) (v : value),
    well_typed g Gamma ->
    well_typed (update (filter_smap g x) x v) Gamma.
  (*intros.
  intro.
  unfold update.
  simpl.
  destruct (x0 =? x)%string eqn:h.
  auto.
  destruct (lookup Gamma x0) eqn:h'; auto;
  destruct (lookup (filter_smap g x) x0) eqn:h'';
  specialize(H0 x0);
  rewrite h' in H0;
  pose proof (lookup_filter g x0 x) as h_f1;
  rewrite h in h_f1;
  specialize (h_f1 eq_refl);
  rewrite h_f1 in h'';
  rewrite h'' in H0;
  try apply H0.
Qed.*)
Admitted.

Lemma subst_rel_after_update:
  forall (Gamma : context L) (g1 g2 : smap) (x : string) (v1 v2 : value) (o t : L.(carrier)),
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

Lemma trace_rel_length :
  forall o tr1 tr2,
    trace_rel o tr1 tr2 ->
    length tr1 = length tr2.
Proof.
  intros o tr1 tr2 Hrel.
  induction Hrel.
  - simpl. f_equal. assumption.
  - simpl. f_equal. assumption.
  - subst. reflexivity.
Qed.

Lemma trace_rel_app :
  forall o t1 t2 t3 t4,
    trace_rel o t1 t3 ->
    trace_rel o t2 t4 ->
    trace_rel o (t1 ++ t2) (t3 ++ t4).
Proof.
  intros o t1 t2 t3 t4 Hrel1 Hrel2.
  revert t2 t4 Hrel2.
  induction Hrel1.
  - intros t2 t4 Hrel2.
    simpl.
    constructor.
    * apply IHHrel1. assumption.
    * assumption.
    * assumption.
  - intros t2 t4 Hrel2.
    simpl.
    apply Decl_Sec.
    * apply IHHrel1. assumption.
    * assumption.
  - intros t2 t4 Hrel2.
    simpl. rewrite H. rewrite H0. simpl. assumption.
Qed.

Lemma H_pull_out_inner_subst : 
  forall x v s n e g,
    x <> s ->
    (subst_many L (filter (fun y => negb (String.eqb (fst y) x)) g) (subst L s n (subst L x v e)))
    = (subst L x v (subst_many L (filter (fun y => negb (String.eqb (fst y) x)) g) (subst L s n e))). 
Proof.
  intros.
  induction g; simpl.
  - apply (subst_neq_id_commute L x s v n e).
    exact H.
  - destruct a; simpl; destruct (String.eqb s0 x) eqn:H_s0_x0; simpl.
    + apply IHg.
    + rewrite (subst_neq_id_commute L x s v n e).
      rewrite (subst_neq_id_commute L x s0 v v0 (subst L s n e)).
      apply (subst_many_subst_commute L x v g (subst L s0 v0 (subst L s n e))).
      apply String.eqb_neq in H_s0_x0.
      apply id_neq_sym in H_s0_x0; exact H_s0_x0.
      exact H.
Qed.

Lemma trace_rel_split :
  forall o e g1 g2 v1 v2 tr1 tr2 tr3 tr4,
  trace_rel o (tr1++tr2) (tr3++tr4) ->
  big_eval L (subst_many L g1 e) v1 tr1 ->
  big_eval L (subst_many L g2 e) v2 tr3 ->
  trace_rel o tr1 tr3 /\ trace_rel o tr2 tr4.
Proof.
intros. revert g1 g2 v1 v2 tr1 tr2 tr3 tr4 H H0 H1. induction e.
{
  intros.
  rewrite subst_many_var in H0, H1.
  destruct lookup in H0; destruct lookup in H1.
  - inversion H0; subst. inversion H1; subst. split.
    * constructor; auto.
    * simpl in H. assumption.
  - inversion H0; subst. inversion H1; subst.
  - inversion H0; subst.
  - inversion H0; subst.
}
{
  intros.
  rewrite subst_many_val in H0, H1.
  inversion H0; subst. inversion H1; subst.
  split.
  - constructor; auto.
  - simpl in H. apply H.
}
{
  intros.
  rewrite subst_many_tm_bin in H0, H1.
  inversion H0; subst. inversion H1; subst.
  specialize (IHe1 g1 g2 v0 v1 tr0 (tr5++tr2) tr1 (tr6++tr4)).
  repeat rewrite <- app_assoc in H.
  specialize (IHe1 H H4 H6).
  inversion IHe1; subst. 
  specialize (IHe2 g1 g2 v3 v4 tr5 tr2 tr6 tr4).
  destruct IHe1 as [IHe11 IHe12].
  specialize (IHe2 IHe12).
  specialize (IHe2 H5 H7).
  destruct IHe2 as [IHe21 IHe22].
  split.
  - apply trace_rel_app.
    * assumption.
    * assumption. 
  - apply IHe22. 
}
{
  intros.
  rewrite subst_many_un in H0, H1.
  inversion H0; subst. inversion H1; subst.
  specialize (IHe g1 g2 v v0 tr1 tr2 tr3 tr4).
  specialize (IHe H H3 H4).
  destruct IHe as [IHe1 IHe2].
  split; assumption.
}
{
  intros.
  rewrite subst_many_let in H0, H1.
  inversion H0; subst. inversion H1; subst.
  specialize (IHe1 g1 g2 v0 v3 tr0 (tr5++tr2) tr1 (tr6++tr4)).
  repeat rewrite <- app_assoc in H.
  specialize (IHe1 H H7 H9).
  inversion IHe1; subst. 
  specialize (IHe2 g1 g2 v1 v2 tr5 tr2 tr6 tr4).
  destruct IHe1 as [IHe11 IHe12].
  specialize (IHe2 IHe12).
  admit.
}
{
  intros.
  rewrite subst_many_declass in H0, H1.
  inversion H0; subst. inversion H1; subst.
  specialize (IHe g1 g2 v1 v2 tr tr2 tr0 tr4) as IHtrace.
  assert (trace_rel o (tr++tr2) (tr0++tr4)) as Hsame. {
    inversion H; subst.
    - apply H9.
    - apply H5.
    - discriminate.
  }
  specialize (IHtrace Hsame H6 H7).
  destruct IHtrace as [IHtrace1 IHtrace2].
  assert (trace_rel o ((v1, c) :: tr) ((v2, c) :: tr0)) as Hsame2. {
    inversion H. 
    - apply Decl_Pub. 
      * assumption.
      * assumption.
      * assumption.
    - apply Decl_Sec.
      * assumption.
      * assumption.
    - discriminate.
  }
  split. apply Hsame2. apply IHtrace2.
}
Admitted.

Lemma H_update_subst_equiv : 
  forall x g v e,
    (subst_many L (update (filter (fun y => negb (String.eqb (fst y) x)) g) x v) e)
    = (subst L x v (subst_many L (filter (fun y => negb (String.eqb (fst y) x)) g) e)). 
  Proof.
  simpl.
  induction g; simpl.
  - reflexivity.
  - destruct a; simpl.
  destruct (negb (String.eqb s x)) eqn:H_eq; simpl.
  + apply Bool.negb_true_iff in H_eq; apply String.eqb_neq in H_eq.
  intros v0 e; specialize (H_pull_out_inner_subst x v0 s v e g); auto.
  + apply IHg.
Qed.

Theorem noninterference (o t : L.(carrier)) (G : context L) (TG : type_context) (e: tm L) (tr1 tr2 : trace L):
  has_type L G e t ->
  has_sem_type o G TG e t.
  intros h.
  induction h.
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h1 rel Hv1 Hv2.
    specialize (h1 x). 
    destruct (lookup g1 x) eqn:E1; [ | (rewrite H in h1; contradiction) ].
    destruct (lookup g2 x) eqn:E2; [ | (rewrite H in h1; contradiction) ].
    rewrite (subst_many_var L g1 x) in Hv1; rewrite E1 in Hv1; simpl in Hv1.
    rewrite (subst_many_var L g2 x) in Hv2; rewrite E2 in Hv2; simpl in Hv2.
    inversion Hv1; subst.
    inversion Hv2; subst.
    rewrite H in h1.
    exact h1.    
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h1 rel h2 h3.
    rewrite subst_many_val in h2.
    rewrite subst_many_val in h3.
    inversion h2; subst.
    inversion h3; subst.
    apply TR_Low.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h1 rel h2 h3.
    rewrite subst_many_un in h2.
    rewrite subst_many_un in h3.
    inversion h2; subst.
    inversion h3; subst.

    destruct (IHh g1 g2 v v0 tr_1 tr_2 wt1 wt2 h1 rel H0 H1); subst; constructor.
    apply H.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h_sub rel h_eval1 h_eval2.
    rewrite subst_many_tm_bin in h_eval1.
    rewrite subst_many_tm_bin in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.
    unfold has_sem_type in IHh1.
    assert (trace_rel o tr0 tr4) as Hqn1. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v1 tr0 tr3 tr4 tr5 rel H1 H3) as [H0rel].
      apply H0rel.
    }
    assert (trace_rel o tr3 tr5) as Hqn2. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v1 tr0 tr3 tr4 tr5 rel H1 H3) as [H0rel].
      apply H.
    }

    destruct (IHh1 g1 g2 v0 v1 tr0 tr4 wt1 wt2 h_sub Hqn1 H1 H3); subst.
    destruct (IHh2 g1 g2 v3 v4 tr3 tr5 wt1 wt2 h_sub Hqn2 H2 H4); subst.
    - simpl.
      constructor.
    - simpl.
      constructor.
      specialize(L.(return_max) t t0). intros.
      destruct H0.
      {
       rewrite H0. 
       specialize(L.(max_le) t0 o t). 
       intros. 
       rewrite H in H5. 
       rewrite H0 in H5. 
       specialize (H5 eq_refl eq_refl).
       apply H5. 
      }
      {
       rewrite H0. apply H. 
      }
      
    -simpl.
     constructor. 
     specialize(L.(return_max) t t2).
     intros.
     destruct H0.
     {
      rewrite H0.
      apply H.
     }
     {
      rewrite H0.
      specialize(L.(max_le) t o t2).
      intros. 
      rewrite H in H5. 
      specialize (L.(order_max) t2 t); intros.
      rewrite H6 in H5.
      rewrite H0 in H5.
      specialize (H5 eq_refl eq_refl).
      apply H5.
     }
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h_sub rel h_eval1 h_eval2.
    rewrite subst_many_let in h_eval1.
    rewrite subst_many_let in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.

    unfold has_sem_type in IHh2.
    specialize (IHh2 (update (filter (fun y => negb (String.eqb (fst y) x)) g1) x v0) (update (filter (fun y => negb (String.eqb (fst y) x)) g2) x v3) 
    v1 v2 tr3 tr5). 

    rewrite (H_update_subst_equiv x g1 v0 e2) in IHh2.
    rewrite (H_update_subst_equiv x g2 v3 e2) in IHh2.
    
    unfold has_sem_type in IHh1.
    apply IHh2.
    apply well_typed_after_update.
    apply wt1.
    apply well_typed_after_update.
    apply wt2.
    apply subst_rel_after_update.
    assert (trace_rel o tr0 tr4) as Hqn1. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v3 tr0 tr3 tr4 tr5 rel H4 H6) as [H0rel _].
      apply H0rel.
    }
    assert (trace_rel o tr3 tr5) as Hqn2. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v3 tr0 tr3 tr4 tr5 rel H4 H6) as [H0rel].
      apply H.
    }
    assert (length tr0 = length tr4) as Hqn3. {
      specialize (trace_rel_length o tr0 tr4) as Hlen.
      specialize (Hlen Hqn1).
      assumption.
    }
    eapply IHh1.
    apply wt1.
    apply wt2.
    apply h_sub.
    apply Hqn1.
    apply H4.
    apply H6.
    apply h_sub.
    assert (trace_rel o tr0 tr4) as Hqn1. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v3 tr0 tr3 tr4 tr5 rel H4 H6) as [H0rel _].
      assumption.
    }
    assert (trace_rel o tr3 tr5) as Hqn2. {
      pose proof (trace_rel_split o e1 g1 g2 v0 v3 tr0 tr3 tr4 tr5 rel H4 H6) as [H0rel].
      apply H.
    }
    apply Hqn2.
    apply H5.
    apply H7.
    }
    {
      unfold has_sem_type.
      intros g1 g2 v1 v2 tr_1 tr_2 wt1 wt2 h_sub rel h_eval1 h_eval2.
      rewrite subst_many_declass in h_eval1.
      rewrite subst_many_declass in h_eval2.
      inversion h_eval1; subst. 
      inversion h_eval2; subst.
      inversion rel.
      
      unfold has_sem_type in IHh.
      destruct (IHh g1 g2 v1 v2 tr tr0 wt1 wt2 h_sub H6 H3 H4).
      -apply TR_Low.
      -destruct (L.(le) Label t) eqn:Hlt.
        *destruct (L.(le) Label o0) eqn:Hlt2.
         {
          subst. apply TR_Low.
         }
         {
          subst. apply TR_Low.
         }
        *destruct (L.(le) Label o0) eqn:Hlt2.
         {
          subst. apply TR_Low.
         }
         {
          subst. apply TR_Low.
         }
      -destruct (L.(le) Label t) eqn:Hlt.
        *destruct (L.(le) Label o0) eqn:Hlt2.
        {
         subst. constructor. destruct H9 as [H91 H92]. apply H91.
        }
        {
          subst. constructor. apply Hlt2.
        }
        *destruct (L.(le) Label o0) eqn:Hlt2.
        {
          subst. constructor. destruct H9 as [H91 H92]. apply H91.
        }
        {
          subst. constructor. apply Hlt2.
        }
      -discriminate.
    }
Qed.

End Noninterference.