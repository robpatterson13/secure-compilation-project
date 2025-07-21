Require Import core fintype systemf.

Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.

(* delta is typically the number of type variables, while m is typically the number of value variables *)

Definition delta_context : Type := nat.

Definition gamma_context (delta : delta_context) (m : nat) := fin m -> ty delta.

Definition prelation (delta : delta_context) ( m : nat ) : Type := list (vl delta m * vl delta m).

Definition type_store (delta : delta_context) : Type := 
  (fin delta) -> (ty 0 * ty 0 * prelation 0 0).

Definition value_store (m : nat) : Type := (fin m) -> vl 0 0 * vl 0 0.

Definition vsubst {delta : delta_context} {m : nat} (v : vl delta m ) :=
  scons v var_vl. 

Definition tsubst { delta : delta_context } (T : ty delta) :=
  scons T var_ty.

Definition lift_gamma {delta : delta_context} {m : nat} (Gamma : gamma_context delta m)
  : gamma_context (S delta) m
  := fun i => ren_ty shift (Gamma i).

Inductive has_type (Delta : delta_context) {m : nat} (Gamma : gamma_context Delta m): 
  tm Delta m -> ty Delta -> Prop :=
| T_Var : forall x,
    has_type Delta Gamma (vt (var_vl x)) (Gamma x)
| T_True : has_type Delta Gamma (vt true) (Core.bool)
| T_False : has_type Delta Gamma (vt false) (Core.bool)
| T_Lam : forall t1 t2 e,
    has_type Delta (scons t1 Gamma) e t2 ->
    has_type Delta Gamma (vt (lam t1 e)) (arr t1 t2)
| T_TLam : forall t e,
    has_type (S Delta) (lift_gamma Gamma) e t ->
    has_type Delta Gamma (vt (tlam e)) (all t)
| T_App : forall t1 t2 e1 e2,
    has_type Delta Gamma e1 (arr t1 t2) ->
    has_type Delta Gamma e2 t1 ->
    has_type Delta Gamma (Core.app e1 e2) t2
| T_TApp : forall t t' e,
    has_type Delta Gamma e (all t) ->
    has_type Delta Gamma (tapp e t') (subst_ty (tsubst t') t)
| T_Pack : forall e t t',
    has_type Delta Gamma (vt e) (subst_ty (tsubst t') t) ->
    has_type Delta Gamma (vt (pack t' e)) (ex t)
| T_Unpack : forall t t2 e1 e2,
    has_type Delta Gamma e1 (ex t) ->
    has_type (S Delta) (scons t (lift_gamma Gamma)) e2 (ren_ty shift t2) ->
    has_type Delta Gamma (unpack e1 e2) t2.

Definition empty_gamma (delta : delta_context) : gamma_context delta 0 :=
  fun (i : fin 0) => match i with end.

 Lemma test_lemma_1 : (has_type 0 (empty_gamma 0)
                            (vt (tlam (vt (lam (var_ty var_zero) (vt (tlam (vt (lam (var_ty var_zero) 
                              (vt (var_vl (shift var_zero))))))))))) 
                            (all (arr (var_ty var_zero) (all (arr (var_ty var_zero) (var_ty (shift var_zero))))))).
Proof.
  repeat constructor.
  specialize (T_Var) as funny.
  specialize (funny 2 2 (scons (var_ty var_zero) (lift_gamma (scons (var_ty var_zero) (lift_gamma (empty_gamma 0))))) (shift var_zero)).
  assumption.
Qed.

Lemma test_lemma_2 : (has_type 3 (empty_gamma 3)  (vt (pack bool true)) (ex (var_ty var_zero))).
Proof.
  repeat constructor.
Qed.

Inductive big_eval {delta m : nat} : tm delta m -> vl delta m -> Prop := 
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

Definition p_1 {delta}
  (ts : type_store delta) : fin delta -> ty 0 :=
  fun i =>
    let '(T1, _T2, _R) := ts i in
    T1.

Definition p_2 {delta}
  (ts : type_store delta) : fin delta -> ty 0 :=
  fun i =>
    let '(_T1, T2, _R) := ts i in
    T2.

Definition t_1 {m}
  (vs : value_store m) : fin m -> vl 0 0 :=
    fun i =>
      match (vs i) with 
      | (v1, v2) => v1
      end.

Lemma t_1c : forall m (vs : value_store m),
  (t_1 vs) = (t_1 vs).
Proof.
  intros.
  unfold t_1.
  reflexivity.
Qed.

Definition t_2 {m}
  (vs : value_store m) : fin m -> vl 0 0 :=
    fun i =>
      match (vs i) with 
      | (v1, v2) => v2
      end. 

Definition well_typed_pair (t1 t2 : ty 0) (p : vl 0 0 * vl 0 0) : Prop :=
  forall (v1 v2 : vl 0 0),
    p = (v1, v2) ->
    has_type 0 (empty_gamma 0) (vt v1) t1 /\ has_type 0 (empty_gamma 0) (vt v2) t2.

Definition related (t1 t2 : ty 0) (R : prelation 0 0) : Prop :=
  Forall (well_typed_pair t1 t2) R. 

Fixpoint SN_V {delta} (T : ty delta) (v1 v2 : vl 0 0) (p : type_store delta) : Prop :=
  match T with
  | (Core.bool)  => (v1 = true /\ v2 = true) \/ (v1 = false /\ v2 = false)
  | (arr t1 t2) =>
      match v1, v2 with
      | (lam t1' b1), (lam t2' b2) => 
        t1' = (subst_ty (p_1 p) t1) /\
        t2' = (subst_ty (p_2 p) t1) /\
        (forall v1' v2', (SN_V t1 v1' v2' p) ->
        ((has_type 0 (empty_gamma 0) (subst_tm var_ty (vsubst v1') b1) (subst_ty (p_1 p) t2)) /\
         (has_type 0 (empty_gamma 0) (subst_tm var_ty (vsubst v2') b2) (subst_ty (p_2 p) t2)) /\
         (exists v1 v2, big_eval (subst_tm var_ty (vsubst v1') b1) v1 /\
                        big_eval (subst_tm var_ty (vsubst v2') b2) v2 /\ 
                        (SN_V t2 v1 v2 p))))
      | _, _ => False
      end
  | (var_ty n) => 
      let '(T1,T2,R) := p n in
      In (v1,v2) R
  | (all t) => 
        match v1, v2 with
        | (tlam b1), (tlam b2) =>
              (forall t1 t2 R,
                (related t1 t2 R) ->
                  ((has_type 0 (empty_gamma 0) (subst_tm (tsubst t1) var_vl b1) (subst_ty (p_1 (scons (t1, t2, R) p)) t)) /\
                  (has_type 0 (empty_gamma 0) (subst_tm (tsubst t2) var_vl b2) (subst_ty (p_2 (scons (t1, t2, R) p)) t)) /\
                  (exists v1 v2, big_eval (subst_tm (tsubst t1) var_vl b1) v1 /\ 
                                 big_eval (subst_tm (tsubst t2) var_vl b2) v2 /\ 
                                 (SN_V t v1 v2 (scons (t1, t2, R) p)))))
        | _, _ => False
        end
  | (ex t) => 
      match v1, v2 with  
      | (pack t1 v1'), (pack t2 v2') =>
        (exists t1' t2', t1 = (subst_ty (p_1 p) t1') /\ t2 = (subst_ty (p_2 p) t2') /\
          (exists R, (related t1 t2 R) /\ (SN_V t v1' v2' (scons (t1, t2, R) p))))
      | _, _ => False
      end
  end.

Definition SN_E {delta} (T : ty delta) (e1 e2 : tm 0 0) (p : type_store delta) : Prop :=
  (has_type 0 (empty_gamma 0) e1 (subst_ty (p_1 p) T)) /\
  (has_type 0 (empty_gamma 0) e2 (subst_ty (p_2 p) T)) /\
  (exists v1 v2, big_eval e1 v1 /\ big_eval e2 v2 /\ (SN_V T v1 v2 p)).

Definition empty_vs : value_store 0 :=
  fun i => match i with end.

Inductive LR_G { delta : delta_context } : forall m,
  value_store m -> gamma_context delta m -> type_store delta -> Prop :=
| G_Empty : forall p, LR_G 0 empty_vs (empty_gamma delta) p
| G_Cons : forall m Gamma' T o v1 v2 p,
  LR_G m o Gamma' p -> 
  SN_V T v1 v2 p ->
  LR_G (S m) (scons (v1, v2) o) (scons T Gamma') p.

Definition ts_empty : type_store 0 :=
  fun i : fin 0 => match i with end.

Definition s0_ty : fin 0 -> ty 0 := p_1 ts_empty.

Require Import FunctionalExtensionality.

Lemma ts_id1 : p_1 (fun i : fin 0 => match i with end) = var_ty.
Proof.
  unfold p_1, ts_empty.
  apply functional_extensionality; intros i.
  destruct i.                        
Qed.

Lemma ts_id2 : p_2 (fun i : fin 0 => match i with end) = var_ty.
Proof.
  unfold p_2, ts_empty.
  apply functional_extensionality; intros i.
  destruct i.                        
Qed.

Lemma vs_id1 : t_1 (fun i : fin 0 => match i with end) = var_vl.
Proof.
  unfold t_1, ts_empty.
  apply functional_extensionality; intros i.
  destruct i.                        
Qed.

Lemma vs_id2 : t_2 (fun i : fin 0 => match i with end) = var_vl.
Proof.
  unfold t_2, ts_empty.
  apply functional_extensionality; intros i.
  destruct i.                        
Qed.

Lemma test_sub : 
  forall (e : tm 0 0),
    (subst_tm var_ty var_vl e) = e.
Proof.
  intros.
  asimpl.
  reflexivity.
Qed.

Lemma test_sub2 :
  forall (e : tm 0 0),
    (subst_tm (p_1 ts_empty) var_vl e) = e.
Proof.
  intros.
  asimpl.
  simpl.
  unfold ts_empty.
  rewrite ts_id1.
  asimpl.
  reflexivity.
Qed.
  
Inductive LR_D : forall delta_context, type_store delta_context -> Prop :=
| D_Empty : LR_D 0 ts_empty 
| D_Cons : forall Delta' p t1 t2 R,
  LR_D Delta' p ->
  related t1 t2 R ->
  LR_D (S Delta') (scons (t1, t2, R) p).

Definition related_lr (Delta : delta_context) { m : nat } (Gamma : gamma_context Delta m) 
                      (e1 e2 : tm Delta m) (T : ty Delta) : Prop :=
  (has_type Delta Gamma e1 T) /\ 
  (has_type Delta Gamma e2 T) /\
  (forall p, (LR_D Delta p) ->
    (forall vs, (LR_G m vs Gamma p) ->  
      (SN_E T (subst_tm (p_1 p) (t_1 vs) e1)  (subst_tm (p_2 p) (t_2 vs) e2) p))).

Lemma compatability_app :
  forall Delta m (Gamma : gamma_context Delta m) e1 e2 t1 t2,
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
  specialize (T_App 0 (empty_gamma 0) (subst_ty (p_1 p) t1) (subst_ty (p_1 p) t2) (subst_tm (p_1 p) (t_1 vs) e1) (subst_tm (p_1 p) (t_1 vs) e2)) as HT2.
  asimpl.
  asimpl in H7. destruct H7.
  specialize (HT2 H7).
  destruct H4. specialize (H9 p H5 vs H6).
  unfold SN_E in H9.
  destruct H9.
  specialize (HT2 H9).
  split.
  assumption.
  specialize (T_App 0 (empty_gamma 0) (subst_ty (p_2 p) t1) (subst_ty (p_2 p) t2) (subst_tm (p_2 p) (t_2 vs) e1) (subst_tm (p_2 p) (t_2 vs) e2)) as HT3.
  destruct H10.
  destruct H8.
  specialize (HT3 H8 H10).
  split.
  assumption.
  destruct H11; destruct H11.
  destruct H12; destruct H12.
  destruct H12.
  destruct H13.
  specialize (E_App (subst_tm (p_1 p) (t_1 vs) e1) (subst_tm (p_1 p) (t_1 vs) e2)) as HE.
  destruct x1; try contradiction.
  destruct x2; try contradiction.
  simpl in H14.
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
  specialize (E_App (subst_tm (p_2 p) (t_2 vs) e1) (subst_tm (p_2 p) (t_2 vs) e2)) as HE2.
  specialize (HE2 t3 t4 x2 x0 H13 H17 H21).
  exists x2.
  split. assumption.
  split. assumption.
  assumption.
Qed.

Lemma compatability_true :
  forall Delta m (Gamma : gamma_context Delta m),
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
  forall Delta m (Gamma : gamma_context Delta m),
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

Lemma subst_lemma1 :
  forall m Delta Gamma e t vs p,
    LR_D Delta p ->
    LR_G m vs Gamma p ->
    has_type Delta Gamma e t ->
    has_type 0 (empty_gamma 0) (subst_tm (p_1 p) (t_1 vs) e) (subst_ty (p_1 p) t).
Proof.
Admitted.

Lemma subst_lemma2 :
  forall m Delta Gamma e t vs p,
    LR_D Delta p ->
    LR_G m vs Gamma p ->
    has_type Delta Gamma e t ->
    has_type 0 (empty_gamma 0) (subst_tm (p_2 p) (t_2 vs) e) (subst_ty (p_2 p) t).
Proof.
Admitted.

Lemma subst_var0 :
  forall T T' e v,
    has_type 0 (scons T (empty_gamma 0)) e T' ->
    has_type 0 (empty_gamma 0) (vt v) T ->
    has_type 0 (empty_gamma 0) (subst_tm var_ty (vsubst v) e) T'.
Proof.
  intros.
Admitted.

Lemma sn_var :
  forall delta m Gamma vs p, LR_G m vs Gamma (p : type_store delta) ->
  forall x, SN_V (Gamma x) (t_1 vs x) (t_2 vs x) p.
Proof.
  intros delta m Gamma vs p HG. 
  induction HG; intros.
  - destruct x.
  - destruct x.
    * simpl. specialize (IHHG f). unfold t_1. unfold t_2. simpl.
      unfold t_1 in IHHG; unfold t_2 in IHHG. simpl in IHHG. assumption. 
    * simpl. unfold t_1; unfold t_2. simpl. exact H.
Qed.

Lemma compatability_lam :
  forall Delta m (Gamma : gamma_context Delta m) e t t',
    related_lr Delta (scons t Gamma) e e t' ->
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
  specialize (T_Lam 0 (empty_gamma 0)) as HL2.
  specialize (HL2).
  split. asimpl.
  specialize (subst_lemma1 m Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl1.
  asimpl in Hsl1.
  assumption.
  split.
  specialize (subst_lemma2 m Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl2.
  asimpl in Hsl2.
  assumption. asimpl. 
  exists (lam (subst_ty (p_1 p) t)
          (subst_tm (p_1 p) (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_1 vs))) e)).
  exists (lam (subst_ty (p_2 p) t)
          (subst_tm (p_2 p) (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_2 vs))) e)).
  split. constructor. split. constructor. split. reflexivity.
  split. reflexivity.
  intros. split.
  specialize (subst_lemma1 m Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl1.
  inversion Hsl1; subst. asimpl in H6. simpl. asimpl.
  specialize (subst_var0 (subst_ty (p_1 p) t) (subst_ty (p_1 p) t') (subst_tm (p_1 p)
          (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_1 vs))) e) v1' H6) as Hsv1.
  asimpl in Hsv1.
  simpl in Hsv1. apply Hsv1. 
  pose (vs1 := (scons (v1', v2') (empty_vs))).
  assert (LR_G 1 vs1 (scons t (empty_gamma Delta)) p) as Hsg. {
    apply G_Cons.
    - apply G_Empty.
    - exact H4.                      
  }
  assert (has_type Delta (scons t (empty_gamma Delta)) (vt (var_vl var_zero)) t) as Hvar0. {
    apply T_Var.
  }
  specialize (subst_lemma1 1 Delta (scons t (empty_gamma Delta)) (vt (var_vl var_zero)) t vs1 p H2 Hsg Hvar0) as winner.
  simpl in winner. assumption.
  split.
  specialize (subst_lemma2 m Delta Gamma (vt (lam t e)) (arr t t') vs p H2 H3 HL) as Hsl2.
  inversion Hsl2; subst. asimpl in H6. simpl. asimpl.
  unfold funcomp. simpl. asimpl. simpl. 
  specialize (subst_var0 (subst_ty (p_2 p) t) (subst_ty (p_2 p) t') (subst_tm (p_2 p)
          (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_2 vs))) e) v2' H6) as Hsv2.
  asimpl in Hsv2. unfold funcomp in Hsv2. simpl in Hsv2. asimpl in Hsv2.
  simpl in Hsv2. apply Hsv2.
  pose (vs1 := (scons (v1', v2') empty_vs)).
  assert (LR_G 1 vs1 (scons t (empty_gamma Delta)) p) as Hsg. {
    apply G_Cons.
    - apply G_Empty.
    - exact H4.                      
  }
  assert (has_type Delta (scons t (empty_gamma Delta)) (vt (var_vl var_zero)) t) as Hvar0. {
    apply T_Var. 
  }
  specialize (subst_lemma2 1 Delta (scons t (empty_gamma Delta))  (vt (var_vl var_zero)) t vs1 p H2 Hsg Hvar0) as winner2.
  simpl in winner2. assumption.
  destruct H1. specialize (H5 p H2 (scons (v1', v2') vs)).
  specialize (G_Cons m Gamma t vs v1' v2' p H3 H4) as Hcons1.
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
     (subst_tm (p_1 p) (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_1 vs))) e)) v1) as Heq. {
    asimpl. simpl. unfold funcomp. simpl. asimpl.
    reflexivity.
  }
  assert (big_eval (subst_tm (p_2 p) (scons v2' (t_2 vs)) e) v2 = big_eval
  (subst_tm var_ty (vsubst v2')
     (subst_tm (p_2 p) (scons (var_vl var_zero) (funcomp (ren_vl id shift) (t_2 vs))) e)) v2) as Heq2. {
    asimpl. simpl. unfold funcomp. simpl. asimpl. reflexivity.
  }
   assert ((t_1 (scons (v1', v2') vs)) = (scons v1' (t_1 vs)))as Hbe1. {
    unfold t_1.

    apply functional_extensionality.
    intros.
    destruct x. simpl.
    reflexivity.
    simpl.
    reflexivity.
  }
  assert ((t_2 (scons (v1', v2') vs)) = (scons v2' (t_2 vs)))as Hbe2. {
    unfold t_2.
    apply functional_extensionality.
    intros.
    destruct x. asimpl.
    reflexivity.
    asimpl.
    reflexivity.
  }
  repeat split.
  - asimpl. asimpl in Heq. rewrite <- Heq. rewrite <- Hbe1. assumption.
  - asimpl. asimpl in Heq2. rewrite <- Heq2. destruct BE2. rewrite <- Hbe2. assumption.
  - destruct BE2. apply H8.
Qed.

Lemma compatability_var :
  forall Delta m (Gamma : gamma_context Delta m) n,
    (related_lr Delta Gamma (vt (var_vl n)) (vt (var_vl n)) (Gamma n)).
Proof.
  intros.
  unfold related_lr.
  split.
  constructor.
  split.
  constructor. 
  intros.
  unfold SN_E.
  split.
  asimpl.
  assert (has_type 0 (empty_gamma 0) (vt (t_1 vs n)) (subst_ty (p_1 p) (Gamma n))) as IHv. { 
    specialize (subst_lemma1 m Delta Gamma (vt (var_vl n)) (Gamma n) vs p) as Hsl1.
    asimpl in Hsl1.
    specialize (T_Var Delta Gamma n) as Htv.
    specialize (Hsl1 H H0 Htv).
    assumption.
  }
  assumption.
  split.
  assert (has_type 0 (empty_gamma 0) (vt (t_2 vs n)) (subst_ty (p_2 p) (Gamma n))) as IHv2. {
    specialize (subst_lemma2 m Delta Gamma (vt (var_vl n)) (Gamma n) vs p) as Hsl2.
    asimpl in Hsl2.
    specialize (T_Var Delta Gamma n) as Htv2.
    specialize (Hsl2 H H0 Htv2).
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
  specialize (Hvar Delta m Gamma vs p H0 n).
  assumption.
Qed.

Lemma fundamental : 
  forall Delta m (Gamma : gamma_context Delta m) e t,
  (has_type Delta Gamma e t) ->
  (related_lr Delta Gamma e e t).
Proof.
Admitted.

Lemma free_theorem_i :
  forall e t v,
  (has_type 0 (empty_gamma 0) e ((all (arr (var_ty var_zero) (var_ty var_zero))))) ->
  (has_type 0 (empty_gamma 0) (vt v) t) ->
  (big_eval (Core.app (tapp e t) (vt v)) v).
Proof.
  intros.
  specialize (fundamental 0 0 (empty_gamma 0) e (all (arr (var_ty var_zero) (var_ty var_zero))) H) as H_fun.
  unfold related_lr in H_fun.
  destruct H_fun. destruct H2.
  specialize (H3 ts_empty D_Empty empty_vs (G_Empty ts_empty)). unfold SN_E in H3.
  destruct H3. destruct H4. destruct H5. destruct H5. destruct H5. destruct H6.
  destruct x; destruct x0; try contradiction.
  assert (related t t [(v , v)]) as H_rel. {
    constructor.
    - unfold well_typed_pair. intros. split; try inversion H8; try subst; try assumption.
    - constructor.
  }
  specialize (H7 t t [(v,v)] H_rel). asimpl in H7.
  destruct H7. destruct H8. destruct H9. destruct H9.
  destruct H9. destruct H10. destruct x; destruct x0; try contradiction.
  unfold p_1 in H11; unfold p_2 in H11. asimpl in H11. destruct H11. destruct H12.
  inversion H11; subst.
  asimpl in H13. specialize (H13 v v).
  destruct H13. simpl. constructor. reflexivity.
  destruct H12. 
  destruct H13. 
  destruct H13. 
  destruct H13. 
  destruct H15.
  simpl in H16.
  specialize (E_App (tapp e t) (vt v) t t3 v v) as E_A.
  unfold ts_empty in H5.
  unfold empty_vs in H5.
  rewrite ts_id1 in H5.
  rewrite vs_id1 in H5.
  asimpl in H5.
  specialize (E_TApp e t t0 (lam t t3) H5 H9) as E_TA.
  specialize (E_A E_TA (E_Val v)). inversion H16.
  - inversion H17; subst. specialize (E_A H13). assumption.
  - contradiction H17. 
Qed.




