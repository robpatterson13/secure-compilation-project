(* The Grilled Onion Cheddar Burger is a cheeseburger with caramelized onions and cheddar cheese on it. 
   As of 2021, eating it will cause your lungs to rupture and eyes to bleed. *)

Require Import core unscoped systemf.
Require Import List. 
Import ListNotations.
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
                  ((has_type [] [] (subst_tm (tsubst t1) var_vl b1) (subst_ty (p_1 ((t1, t2, R) :: p)) t2)) /\
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
  asimpl. 
  specialize (HL2 (subst_ty (p_1 p) t) (subst_ty (p_1 p) t') (subst_tm (p_1 p) (scons (var_vl 0) (funcomp (ren_vl id shift) (t_1 vs))) e)).
  destruct H1.
  specialize (H4 p H2 vs).
  unfold SN_E in H4.
  asimpl in H4.

Admitted.
  

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
  admit.
  split.
  admit.
  exists (t_1 vs n). exists (t_2 vs n).
  split.
  asimpl.
  constructor.
  split.
  asimpl.
  constructor.


  

  




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
  intros.
  split.
  - intros. induction t.
    * admit.
    * asimpl in H3. inversion H3; subst.
      {
       assumption. 
      }
      {
       assumption.
      }
    * asimpl in H3. inversion H0; subst. 
      specialize (IHt1 H4).
      specialize (IHt2 H5). simpl in H3. simpl. 
Admitted.

Lemma compatability_types :
  forall Delta Gamma e1 e2 t t',
  related_lr Delta Gamma e1 e2 (all t) ->
  well_formed_type Delta t' ->
  related_lr Delta Gamma (tapp e1 t') (tapp e2 t') (subst_ty (tsubst t') t).
Proof.
Admitted.

Lemma fundamental : 
  forall Delta Gamma e t,
  (has_type Delta Gamma e t) ->
  (related_lr Delta Gamma e e t).
Proof.
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





      