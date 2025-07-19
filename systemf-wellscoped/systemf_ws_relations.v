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
      let '(v1, _v2) := vs i in
      v1.

Definition t_2 {m}
  (vs : value_store m) : fin m -> vl 0 0 :=
    fun i =>
      let '(_v1, v2) := vs i in
      v2.

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

  