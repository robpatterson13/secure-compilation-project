Require Import core unscoped systemf.
Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.

Definition gamma_context := list ty.

Definition delta_context := list unit. 

Definition prelation := list (vl * vl).

Definition type_store := list (ty * ty * prelation).
  
Definition value_store := list (vl * vl).

Definition gamma_lookup (G : gamma_context) (x : nat) : option ty :=
  nth_error G x.

Definition delta_lookup (D : delta_context) (x : nat) : option unit :=
  nth_error D x. 

Definition vsubst (v : vl) :=
  scons v var_vl. 

Definition tsubst T:=
  scons T var_ty.

Definition lift_ty t := ren_ty shift t.

Definition lift_ctx Gamma := map lift_ty Gamma.

Definition dshift (n : nat) : nat :=
  match n with
  | 0   => 0          
  | S k => k          
  end.

Definition ty_dshift (t : ty) : ty := ren_ty dshift t.

Fixpoint well_formed_type (Delta : delta_context) (t : ty) : Prop :=
  match t with 
  | bool => True
  | (var_ty n) => n < (length Delta) 
  | (arr t1 t2) => well_formed_type Delta t1 /\ well_formed_type Delta t2
  | (all t) => well_formed_type (tt :: Delta) t
  | (ex t) => well_formed_type (tt :: Delta) t
  end.

Fixpoint well_formed_type_restrict (Delta : delta_context) (t : ty) (r : nat) : Prop :=
  match t with 
  | bool => True
  | (var_ty n) => n < (length Delta) /\ (n <> r)
  | (arr t1 t2) => well_formed_type_restrict Delta t1 r /\ well_formed_type_restrict Delta t2 r
  | (all t) => well_formed_type_restrict (tt :: Delta) t (S r)
  | (ex t) => well_formed_type_restrict (tt :: Delta) t (S r)
  end.


Inductive has_type : delta_context -> gamma_context -> tm -> ty -> Prop :=
| T_Var : forall Delta Gamma x t1,
    gamma_lookup Gamma x = Some t1 ->
    has_type Delta Gamma (vt (var_vl x)) t1
| T_True : forall Delta Gamma,
    has_type Delta Gamma (vt true) (Core.bool) 
| T_False : forall Delta Gamma,
    has_type Delta Gamma (vt false) (Core.bool) 
| T_Lam : forall Delta Gamma t1 t2 e,
    has_type Delta (t1 :: Gamma) e t2 ->
    has_type Delta Gamma (vt (lam t1 e)) (arr t1 t2)
| T_TLam : forall Delta Gamma t e,
    has_type (tt :: Delta) (lift_ctx Gamma) e t ->
    has_type Delta Gamma (vt (tlam e)) (all t)
| T_App : forall Delta Gamma t1 t2 e1 e2,
    has_type Delta Gamma e1 (arr t1 t2) ->
    has_type Delta Gamma e2 t1 ->
    has_type Delta Gamma (Core.app e1 e2) t2 
| T_TApp : forall Delta Gamma t t' e,
    has_type Delta Gamma e (all t) ->
    well_formed_type Delta t' ->
    has_type Delta Gamma (tapp e t') (subst_ty (tsubst t') t)
| T_Pack : forall Delta Gamma e t t',
    has_type Delta Gamma (vt e) (subst_ty (tsubst t') t) ->
    well_formed_type Delta t' ->
    has_type Delta Gamma (vt (pack t' e)) (ex t)
| T_Unpack : forall Delta Gamma t t2 e1 e2,
    has_type Delta Gamma e1 (ex t) ->
    has_type (tt :: Delta) (t :: (lift_ctx Gamma)) e2 t2 ->
    well_formed_type_restrict Delta t2 0 ->
    has_type Delta Gamma (unpack e1 e2) (ty_dshift t2).

Lemma test_lemma_1 : (has_type [] [] 
                            (vt (tlam (vt (lam (var_ty 0) (vt (tlam (vt (lam (var_ty 0) (vt (var_vl 1)))))))))) 
                            (all (arr (var_ty 0) (all (arr (var_ty 0) (var_ty 1)))))).
Proof.
  repeat constructor.
Qed.

Lemma test_lemma_2 : (has_type [tt; tt; tt] []  (vt (pack bool true)) (ex (var_ty 0))).
Proof.
  repeat constructor.
Qed.

Lemma well_formed_lemma_test : (well_formed_type [tt; tt; tt] (var_ty 0)).
Proof.
  constructor.
  constructor.
  constructor.
Qed.

Inductive is_value : tm -> Prop :=
| V_lam : forall T t,
    is_value (vt (lam T t))
| V_tlam : forall t,
    is_value (vt (tlam t))
| V_true : is_value (vt true)
| V_false : is_value (vt false).

Inductive big_eval : tm -> vl -> Prop := 
| E_Val : forall v,
    big_eval (vt v) v
| E_App : forall e1 e2 T t v v2,
    big_eval e1 (lam T t) ->
    big_eval e2 v2 ->
    big_eval (subst_tm var_ty (vsubst v2) t) v ->
    big_eval (Core.app e1 e2) v
| E_TApp : forall e T t v,
    big_eval e (tlam t) ->
    big_eval (subst_tm (tsubst T) var_vl t) v ->
    big_eval (tapp e T) v
| E_Unpack : forall t' v e v1,
    big_eval (subst_tm (tsubst t') (vsubst v) e) v1 ->
    big_eval (unpack (vt (pack t' v)) e) v1.


Definition well_typed_pair (t1 t2 : ty) (p : vl * vl) : Prop :=
  forall (v1 v2 : vl),
    p = (v1, v2) ->
    has_type [] [] (vt v1) t1 /\ has_type [] [] (vt v2) t2.

Definition related (t1 t2 : ty) (R : prelation) : Prop :=
  Forall (well_typed_pair t1 t2) R. 

Definition ts_lookup (p : type_store) (a : nat)
  : option (ty * ty * prelation) :=
  nth_error p a.

Definition in_rel (v1 v2 : vl) (R : prelation) : Prop :=
  In (v1 , v2) R.

Fixpoint p_1 (ts : type_store) : nat -> ty :=
  match ts with
  | [] => var_ty   
  | (T , _ , _) :: ts' => scons T (p_1 ts')
  end.

Fixpoint t_1 (vs : value_store) : nat -> vl :=
  match vs with
  | [] => var_vl   
  | (V , _) :: vs' => scons V (t_1 vs')
  end.

Fixpoint t_2 (vs : value_store) : nat -> vl :=
  match vs with
  | [] => var_vl   
  | (_ , V) :: vs' => scons V (t_2 vs')
  end.

Fixpoint p_2 (ts : type_store) : nat -> ty :=
  match ts with
  | [] => var_ty   
  | ( _ , T , _) :: ts' => scons T (p_2 ts')
  end.

Fixpoint vs_1 (ts : value_store) : nat -> vl :=
  match ts with
  | [] => var_vl   
  | (T , _) :: vs' => scons T (vs_1 vs')
  end.

Fixpoint vs_2 (ts : value_store) : nat -> vl :=
  match ts with
  | [] => var_vl   
  | (_, T) :: vs' => scons T (vs_2 vs')
  end.

Fixpoint SN_V (T : ty) (v1 v2 : vl) (p : type_store) : Prop :=
  match T with
  | (Core.bool)  => (v1 = true /\ v2 = true) \/ (v1 = false /\ v2 = false)
  | (arr t1 t2) =>
      match v1, v2 with
      | (lam t1' b1), (lam t2' b2) => 
        t1' = (subst_ty (p_1 p) t1) /\
        t2' = (subst_ty (p_2 p) t1) /\
        (forall v1' v2', (SN_V t1 v1' v2' p) ->
        ((has_type [] [] (subst_tm var_ty (vsubst v1') b1) (subst_ty (p_1 p) t2)) /\
         (has_type [] [] (subst_tm var_ty (vsubst v2') b2) (subst_ty (p_2 p) t2)) /\
         (exists v1 v2, big_eval (subst_tm var_ty (vsubst v1') b1) v1 /\
                        big_eval (subst_tm var_ty (vsubst v2') b2) v2 /\ 
                        (SN_V t2 v1 v2 p))))
      | _, _ => False
      end
  | (var_ty n) => match ts_lookup p n with
                  | Some (_, _, R) => (in_rel v1 v2 R)
                  | None => False
                  end
  | (all t) => 
        match v1, v2 with
        | (tlam b1), (tlam b2) =>
              (forall t1 t2 R,
                (related t1 t2 R) ->
                  ((has_type [] [] (subst_tm (tsubst t1) var_vl b1) (subst_ty (p_1 ((t1, t2, R) :: p)) t1)) /\
                  (has_type [] [] (subst_tm (tsubst t2) var_vl b2) (subst_ty (p_2 ((t1, t2, R) :: p)) t2)) /\
                  (exists v1 v2, big_eval (subst_tm (tsubst t1) var_vl b1) v1 /\ 
                                 big_eval (subst_tm (tsubst t2) var_vl b2) v2 /\ 
                                 (SN_V t v1 v2 ((t1, t2, R) :: p)))))
        | _, _ => False
        end
  | (ex t) => 
      match v1, v2 with  
      | (pack t1 v1'), (pack t2 v2') =>
        (exists t1' t2', t1 = (subst_ty (p_1 p) t1') /\ t2 = (subst_ty (p_2 p) t2') /\
          (exists R, (related t1 t2 R) /\ (SN_V t v1' v2' ((t1, t2, R) :: p))))
      | _, _ => False
      end
  end.

Definition SN_E (T : ty) (e1 e2 : tm) (p : type_store) : Prop :=
  (has_type [] [] e1 (subst_ty (p_1 p) T)) /\
  (has_type [] [] e2 (subst_ty (p_2 p) T)) /\
  (exists v1 v2, big_eval e1 v1 /\ big_eval e2 v2 /\ (SN_V T v1 v2 p)).

Inductive SN_G : list ty -> value_store -> type_store -> Prop :=
| G_Empty : forall p, SN_G nil [] p
| G_Cons : forall Gamma' T o v1 v2 p,
  SN_G Gamma' o p ->
  SN_V T v1 v2 p ->
  SN_G (T :: Gamma') ((v1, v2) :: o) p.

Inductive SN_D : delta_context -> type_store -> Prop :=
| D_Empty : SN_D [] []
| D_Cons : forall Delta' p t1 t2 R,
  SN_D Delta' p ->
  related t1 t2 R ->
  SN_D (tt :: Delta') ((t1, t2, R):: p).

Definition related_lr (Delta : delta_context) (Gamma : gamma_context) (e1 e2 : tm) (T : ty) : Prop :=
  (has_type Delta Gamma e1 T) /\ 
  (has_type Delta Gamma e2 T) /\
  (forall p, (SN_D Delta p) ->
    (forall vs, (SN_G Gamma vs p) ->  
      (SN_E T (subst_tm (p_1 p) (t_1 vs) e1)  (subst_tm (p_2 p) (t_2 vs) e2) p))).


Definition set_is_lr (p : type_store) (R : prelation) (t : ty) : Prop :=
  forall v1 v2,
  ((SN_V t v1 v2 p) ->
  In (v1, v2) R) /\ 
  (In (v1, v2) R ->
  (SN_V t v1 v2 p)).

Lemma sn_var :
  forall Gamma vs p, SN_G Gamma vs p ->
  forall x t, gamma_lookup Gamma x = Some t -> SN_V t (t_1 vs x) (t_2 vs x) p.
Proof.
  intros Gamma vs p HG. 
  induction HG; intros x t Hlk; simpl in Hlk.
  - destruct x. inversion Hlk. inversion Hlk.
  - destruct x; simpl in Hlk.
    * inversion Hlk; subst. simpl. assumption.
    * apply IHHG. assumption.
Qed.

(* Substitutional Lemmas *)

Lemma subst_lemma1 :
  forall Delta Gamma e t vs p,
    SN_D Delta p ->
    SN_G Gamma vs p ->
    has_type Delta Gamma e t ->
    has_type [] [] (subst_tm (p_1 p) (t_1 vs) e) (subst_ty (p_1 p) t).
Proof.
Admitted.

Lemma subst_lemma2 :
  forall Delta Gamma e t vs p,
    SN_D Delta p ->
    SN_G Gamma vs p ->
    has_type Delta Gamma e t ->
    has_type [] [] (subst_tm (p_2 p) (t_2 vs) e) (subst_ty (p_2 p) t).
Proof.
Admitted.

Lemma subst_var0 :
  forall T T' e v,
    has_type [] [T] e T' ->
    has_type [] [] (vt v) T ->
    has_type [] [] (subst_tm var_ty (vsubst v) e) T'.
Proof.
Admitted.

Lemma compositionality : 
  forall Delta t' t p R,
    well_formed_type Delta t' ->
    well_formed_type (tt :: Delta) t ->
    (SN_D Delta p) ->
    set_is_lr p R t' -> (forall v1 v2,
    (SN_V (subst_ty (tsubst t') t) v1 v2 p ->
    SN_V t v1 v2 (((subst_ty (p_1 p) t') , (subst_ty (p_2 p) t'), R) :: p)) 
    /\
    (SN_V t v1 v2 (((subst_ty (p_1 p) t') , (subst_ty (p_2 p) t'), R) :: p) ->
    SN_V (subst_ty (tsubst t') t) v1 v2 p)).
Proof.
Admitted.



Lemma compatability_tlam :
  forall Delta Gamma e t,
    related_lr (tt::Delta) (lift_ctx Gamma) e e t ->
    related_lr Delta Gamma (vt (tlam e)) (vt (tlam e)) (all t).
Proof.
  intros.
  unfold related_lr.
  inversion H; subst. destruct H1.
  specialize (T_TLam Delta Gamma t e H0) as Htl.
  split.
  assumption.
  split.
  assumption.
  intros.
  unfold SN_E.

  repeat split.
  - specialize (subst_lemma1 Delta Gamma (vt (tlam e)) (all t) vs p H3 H4 Htl) as Hsl1.
    assumption.
  - specialize (subst_lemma2 Delta Gamma (vt (tlam e)) (all t) vs p H3 H4 Htl) as Hsl2.
    assumption.
  - unfold SN_E in H2.
    asimpl. 
    exists (tlam (subst_tm (scons (var_ty 0) (funcomp (ren_ty shift) (p_1 p))) (funcomp (ren_vl shift id) (t_1 vs)) e)).
    exists (tlam (subst_tm (scons (var_ty 0) (funcomp (ren_ty shift) (p_2 p))) (funcomp (ren_vl shift id) (t_2 vs)) e)).
    split. constructor. split. constructor. constructor.
    * asimpl. simpl. 
      inversion Htl; subst. unfold funcomp. simpl. asimpl. 
      assert (Hsd : SN_D (tt :: Delta) ((t1, t2, R)::p)). {
        apply D_Cons.
        - assumption.
        - assumption.
      }
      specialize (H2 ((t1, t2, R)::p) Hsd vs).
      assert (Hg1 : SN_G (lift_ctx Gamma) vs ((t1, t2, R) :: p)). {
          admit.
      }
      specialize (H2 Hg1).
      simpl in H2.
      destruct H2.
      destruct H6.
      inversion Htl; subst.
        
Admitted.

Lemma big_eval_ext e1 e2 v :
  e1 = e2 ->
  big_eval e1 v = big_eval e2 v.
Proof. intros ->; reflexivity. Qed.

Lemma compatability_lam :
  forall Delta Gamma e t t',
    related_lr Delta (t :: Gamma) e e t' ->
    related_lr Delta Gamma (vt (lam t e)) (vt (lam t e)) (arr t t').
Proof.
  intros.
  unfold related_lr.
  inversion H; subst.
  specialize (T_Lam Delta Gamma t t' e H0) as HL.
  split.
  assumption.
  split.
  assumption.
  intros.
  unfold SN_E.
  specialize (T_Lam [] []) as HL2.
  specialize (HL2).
  split. asimpl.
  specialize (subst_lemma1 Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl1.
  asimpl in Hsl1.
  constructor.
  inversion Hsl1; subst. asimpl in H7.
  assumption.
  split.
  specialize (subst_lemma2 Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl2.
  asimpl in Hsl2.
  constructor.
  inversion Hsl2; subst. asimpl in H7.
  assumption. asimpl. 
  exists (lam (subst_ty (p_1 p) t)
          (subst_tm (p_1 p) (scons (var_vl 0) (funcomp (ren_vl id shift) (t_1 vs))) e)).
  exists (lam (subst_ty (p_2 p) t)
          (subst_tm (p_2 p) (scons (var_vl 0) (funcomp (ren_vl id shift) (t_2 vs))) e)).
  split. constructor. split. constructor. constructor. reflexivity.
  split. reflexivity.
  intros. split.
  specialize (subst_lemma1 Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl1.
  inversion Hsl1; subst. asimpl in H8. simpl. asimpl.
  specialize (subst_var0 (subst_ty (p_1 p) t) (subst_ty (p_1 p) t') (subst_tm (p_1 p)
          (scons (var_vl 0) (funcomp (ren_vl id shift) (t_1 vs))) e) v1' H8) as Hsv1.
  asimpl in Hsv1.
  simpl in Hsv1. apply Hsv1. 
  pose (vs1 := (v1', v2') :: nil).
  assert (SN_G (t :: nil) vs1 p) as Hsg. {
    apply G_Cons.
    - apply G_Empty.
    - exact H4.                      
  }
  assert (has_type Delta [t] (vt (var_vl 0)) t) as Hvar0. {
    apply T_Var.
    simpl. reflexivity. 
  }
  specialize (subst_lemma1 Delta (t :: nil)  (vt (var_vl 0)) t vs1 p H2 Hsg Hvar0) as winner.
  simpl in winner. assumption.
  split.
  specialize (subst_lemma2 Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl2.
  inversion Hsl2; subst. asimpl in H8. simpl. asimpl.
  specialize (subst_var0 (subst_ty (p_2 p) t) (subst_ty (p_2 p) t') (subst_tm (p_2 p)
          (scons (var_vl 0) (funcomp (ren_vl id shift) (t_2 vs))) e) v2' H8) as Hsv2.
  asimpl in Hsv2.
  simpl in Hsv2. apply Hsv2.
  pose (vs1 := (v1', v2') :: nil).
  assert (SN_G (t :: nil) vs1 p) as Hsg. {
    apply G_Cons.
    - apply G_Empty.
    - exact H4.                      
  }
  assert (has_type Delta [t] (vt (var_vl 0)) t) as Hvar0. {
    apply T_Var.
    simpl. reflexivity. 
  }
  specialize (subst_lemma2 Delta (t :: nil)  (vt (var_vl 0)) t vs1 p H2 Hsg Hvar0) as winner2.
  simpl in winner2. assumption.
  destruct H1. specialize (H5 p H2 ((v1', v2')::vs)).
  specialize G_Cons as Hcons1.
  specialize (Hcons1 Gamma t vs v1' v2' p H3 H4).
  specialize (H5 Hcons1). unfold SN_E in H5.
  destruct H5.
  destruct H6.
  simpl in H7.
  destruct H7 as [v1].
  destruct H7 as [v2].
  destruct H7 as [BE1 BE2].
  exists v1, v2.
  assert (big_eval (subst_tm (p_1 p) (scons v1' (t_1 vs)) e) v1 = big_eval
  (subst_tm var_ty (vsubst v1')
     (subst_tm (p_1 p) (scons (var_vl 0) (funcomp (ren_vl id shift) (t_1 vs))) e)) v1) as Heq. {
    asimpl. simpl.
      assert (He_env : forall n,
            (scons v1' (t_1 vs) : nat -> vl) n =
            (scons v1'
               (funcomp (subst_vl var_ty (funcomp (vsubst v1') shift))
                        (t_1 vs))) n).
    {
      intro n; destruct n; simpl; auto.
      unfold funcomp. simpl. asimpl. reflexivity.
    }
    apply big_eval_ext.
    specialize (ext_tm (p_1 p) (scons v1' (t_1 vs)) (p_1 p) (scons v1'
     (funcomp (subst_vl var_ty (funcomp (vsubst v1') shift))
              (t_1 vs))) (fun _ => eq_refl) He_env e) as Hi. 
    assumption.
  }
  assert (big_eval (subst_tm (p_2 p) (scons v2' (t_2 vs)) e) v2 = big_eval
  (subst_tm var_ty (vsubst v2')
     (subst_tm (p_2 p) (scons (var_vl 0) (funcomp (ren_vl id shift) (t_2 vs))) e)) v2) as Heq2. {
    asimpl. simpl. 
    assert (He_env : forall n,
            (scons v2' (t_2 vs) : nat -> vl) n =
            (scons v2'
               (funcomp (subst_vl var_ty (funcomp (vsubst v2') shift))
                        (t_2 vs))) n).
    {
      intro n; destruct n; simpl; auto.
      unfold funcomp. simpl. asimpl. reflexivity.
    }
    apply big_eval_ext.
    specialize (ext_tm (p_2 p) (scons v2' (t_2 vs)) (p_2 p) (scons v2'
     (funcomp (subst_vl var_ty (funcomp (vsubst v2') shift))
              (t_2 vs))) (fun _ => eq_refl) He_env e) as Hi. 
    assumption.
  }
  repeat split.
  - asimpl. asimpl in Heq. rewrite <- Heq. assumption.
  - asimpl. asimpl in Heq2. rewrite <- Heq2. destruct BE2. assumption.
  - destruct BE2. apply H8.
Qed.
    
Lemma compatability_tapp :
  forall Delta Gamma e t t',
    related_lr Delta Gamma e e (all t) ->
    well_formed_type Delta t' ->
    related_lr Delta Gamma (tapp e t') (tapp e t') (subst_ty (tsubst t') t).
Proof.
  intros.
  unfold related_lr.
  repeat split; inversion H; subst.
  - specialize (T_TApp) as Hta.
    specialize (Hta Delta Gamma t t' e H1 H0).
    assumption.
  - specialize (T_TApp) as Hta.
    specialize (Hta Delta Gamma t t' e H1 H0).
    assumption.
  - specialize (subst_lemma1 Delta Gamma (tapp e t') (subst_ty (tsubst t') t) vs p) as Hs1.
    specialize (Hs1 H1 H2).
    specialize (T_TApp Delta Gamma t t' e) as Htapp.
    specialize (Htapp H3 H0).
    specialize (Hs1 Htapp).
    assumption.
  - specialize (subst_lemma2 Delta Gamma (tapp e t') (subst_ty (tsubst t') t) vs p) as Hs2.
    specialize (Hs2 H1 H2).
    specialize (T_TApp Delta Gamma t t' e) as Htapp.
    specialize (Htapp H3 H0).
    specialize (Hs2 Htapp).
    assumption.
  - unfold SN_E in H4.
    destruct H4.
    specialize (H5 p H1 vs H2).
    destruct H5.
    destruct H6.
    specialize (E_TApp) as HEtapp.
    asimpl.
    destruct H7.
    destruct H7.
    destruct H7.
    destruct H8.
    destruct x; try contradiction.
    destruct x0; try contradiction.
    simpl in H9.
    specialize (H9 (subst_ty (p_1 p) t') (subst_ty (p_2 p) t') []) as H91.
    assert (related (subst_ty (p_1 p) t') (subst_ty (p_2 p) t') []) as Hrel. {
      constructor.
    }
    specialize (H91 Hrel).
    destruct H91.
    destruct H11.
    destruct H12. destruct H12. destruct H12. destruct H13.
    specialize (HEtapp (subst_tm (p_1 p) (t_1 vs) e) (subst_ty (p_1 p) t') t0 x H7 H12).
    specialize (E_TApp) as HEtapp2.
    specialize (H9 (subst_ty (p_1 p) t') (subst_ty (p_2 p) t') []) as H92.
    assert (related (subst_ty (p_1 p) t') (subst_ty (p_2 p) t') []) as Hrel2. {
      constructor.
    }
    specialize (H92 Hrel2).
    destruct H92.
    destruct H16.
    destruct H17. destruct H17.
    destruct H17.
    destruct H18.
    specialize (HEtapp2 (subst_tm (p_2 p) (t_2 vs) e) (subst_ty (p_2 p) t') t1 x2 H8 H18).
    exists x. exists x2.
    split.
    assumption.
    split.
    assumption.
    specialize (compositionality _ t' t p [] H0 ) as Hc.
    unfold related_lr in H.
  Admitted.

Lemma compatability_app :
  forall Delta Gamma e1 e2 t1 t2,
    related_lr Delta Gamma e1 e1 (arr t1 t2) ->
    related_lr Delta Gamma e2 e2 t1 ->
    related_lr Delta Gamma (Core.app e1 e2) (Core.app e1 e2) t2.
Proof.
  intros.
  unfold related_lr.
  inversion H; subst; inversion H0; subst.
  specialize (T_App Delta Gamma t1 t2 e1 e2 H1 H3) as HT.
  split.
  assumption.
  split.
  assumption.
  intros.
  unfold SN_E.
  destruct H2. specialize (H7 p H5 vs H6). unfold SN_E in H7.
  specialize (T_App [] [] (subst_ty (p_1 p) t1) (subst_ty (p_1 p) t2) (subst_tm (p_1 p) (t_1 vs) e1) (subst_tm (p_1 p) (t_1 vs) e2)) as HT2.
  asimpl.
  asimpl in H7. destruct H7.
  specialize (HT2 H7).
  destruct H4. specialize (H9 p H5 vs H6).
  unfold SN_E in H9.
  destruct H9.
  specialize (HT2 H9).
  split.
  assumption.
  specialize (T_App [] [] (subst_ty (p_2 p) t1) (subst_ty (p_2 p) t2) (subst_tm (p_2 p) (t_2 vs) e1) (subst_tm (p_2 p) (t_2 vs) e2)) as HT3.
  destruct H10.
  destruct H8.
  specialize (HT3 H8 H10).
  split.
  assumption.
  specialize (E_App) as HE.
  destruct H11; destruct H11.
  destruct H12; destruct H12.
  destruct H12.
  destruct H13.
  specialize (HE (subst_tm (p_1 p) (t_1 vs) e1) (subst_tm (p_1 p) (t_1 vs) e2)).
  simpl in H14.
  induction x1; try contradiction.
  induction x2; try contradiction.
  destruct H14.
  destruct H15.
  destruct H11. destruct H17.
  specialize (H16 x x0 H18).
  destruct H16.
  destruct H19.
  destruct H20. destruct H20.
  destruct H20.
  destruct H21.
  specialize (HE t t0 x1).
  specialize (HE x H12 H11 H20).
  exists x1.
  specialize (E_App) as HE2.
  specialize (HE2 (subst_tm (p_2 p) (t_2 vs) e1) (subst_tm (p_2 p) (t_2 vs) e2)).
  specialize (HE2 t3 t4 x2 x0 H13 H17 H21).
  exists x2.
  split. assumption.
  split. assumption.
  assumption.
Qed.
  
Lemma compatability_true :
  forall Delta Gamma,
    (related_lr Delta Gamma (vt true) (vt true) bool).
Proof.
  intros.
  constructor.
  - constructor.
  - split.
    * constructor.
    * intros. constructor.
      {
       asimpl. constructor. 
      }
      {
       asimpl. split. constructor.
       - exists true. exists true. split.
         * constructor.   
         * split. constructor. constructor. split. reflexivity. reflexivity.
      }
Qed.

Lemma compatability_false :
  forall Delta Gamma,
    (related_lr Delta Gamma (vt false) (vt false) bool).
Proof.
  intros.
  constructor.
  - constructor.
  - split.
    * constructor.
    * intros. constructor.
      {
       asimpl. constructor. 
      }
      {
       asimpl. split. constructor.
       - exists false. exists false. split.
         * constructor.   
         * split. constructor. simpl. right. split. reflexivity. reflexivity.
      }
Qed.

Lemma compatability_var :
  forall Delta Gamma n t1,
    (gamma_lookup Gamma n) = Some t1 ->
    (related_lr Delta Gamma (vt (var_vl n)) (vt (var_vl n)) t1).
Proof.
  intros.
  unfold related_lr.
  split.
  constructor. apply H.
  split.
  constructor. apply H.
  intros.
  unfold SN_E.
  split.
  asimpl.
  assert (has_type [] [] (vt (t_1 vs n)) (subst_ty (p_1 p) t1)) as IHv. { 
    specialize (subst_lemma1 Delta Gamma (vt (var_vl n)) t1 vs p) as Hsl1.
    asimpl in Hsl1.
    specialize (T_Var Delta Gamma n t1 H) as Htv.
    specialize (Hsl1 H0 H1 Htv).
    assumption.
  }
  assumption.
  split.
  assert (has_type [] [] (vt (t_2 vs n)) (subst_ty (p_2 p) t1)) as IHv2. {
    specialize (subst_lemma2 Delta Gamma (vt (var_vl n)) t1 vs p) as Hsl2.
    asimpl in Hsl2.
    specialize (T_Var Delta Gamma n t1 H) as Htv2.
    specialize (Hsl2 H0 H1 Htv2).
    assumption.
  }
  assumption.
  exists (t_1 vs n). exists (t_2 vs n).
  split.
  asimpl.
  constructor.
  split.
  asimpl.
  constructor.
  specialize sn_var as Hvar.
  specialize (Hvar Gamma vs p H1 n t1 H).
  assumption.
Qed.

Lemma fundamental : 
  forall Delta Gamma e t,
  (has_type Delta Gamma e t) ->
  (related_lr Delta Gamma e e t).
Proof.
  intros.
  induction H.
  - specialize (compatability_var Delta Gamma x t1 H) as Hv.
    assumption.
  - specialize (compatability_true Delta Gamma) as Ht.
    assumption.
  - specialize (compatability_false Delta Gamma) as Hf.
    assumption.
  - specialize (compatability_lam Delta Gamma e t1 t2 IHhas_type) as Hl.
    assumption.
  - specialize (compatability_tlam Delta Gamma e t IHhas_type) as Htl.
    assumption.
  - specialize (compatability_app Delta Gamma e1 e2 t1 t2 IHhas_type1 IHhas_type2) as Ha.
    assumption.
  - specialize (compatability_tapp Delta Gamma e t t' IHhas_type H0) as Hta.
    assumption.
  - admit.
  - admit.
Admitted.

Lemma free_theorem_i :
  forall e t v,
  (has_type [] [] e ((all (arr (var_ty 0) (var_ty 0))))) ->
  (well_formed_type [] t) ->
  (has_type [] [] (vt v) t) ->
  (big_eval (Core.app (tapp e t) (vt v)) v).
Proof.
intros.
specialize (fundamental [] [] e (all (arr (var_ty 0) (var_ty 0))) H) as H_fun.
unfold related_lr in H_fun.
destruct H_fun; destruct H3.
specialize (H4 [] D_Empty [] (G_Empty [])). asimpl in H4. unfold SN_E in H4.
destruct H4. destruct H5. destruct H6. destruct H6. destruct H6. destruct H7.
destruct x; destruct x0; try contradiction H8.
assert (related t t [(v, v)]) as H_rel. {
  constructor.
  - unfold well_typed_pair. intros. split; try inversion H9; try subst; try assumption.
  - constructor.
}
specialize (H8 t t [(v,v)] H_rel). asimpl in H8.
destruct H8. destruct H9. destruct H10; destruct H10.
destruct H10. destruct H11. destruct x; destruct x0; try contradiction H12.
unfold p_1 in H12; unfold p_2 in H12.  asimpl in H12. destruct H12. destruct H13.
inversion H12; subst.
asimpl in H14. specialize (H14 v v). 
destruct H14. simpl. constructor. reflexivity.
destruct H13.
destruct H14.
destruct H14.
destruct H14.
destruct H16. 
simpl in H17.
specialize (E_App) as E_A.
specialize (E_A (tapp e t) (vt v) t t3 v v).
specialize (E_TApp) as E_TA.
specialize (E_TA e t t0 (lam t t3) H6 H10).
specialize (E_A E_TA (E_Val v)). unfold in_rel in H17. inversion H17.
- inversion H18; subst. specialize (E_A H14). assumption. 
- contradiction H18.
Qed. 





      