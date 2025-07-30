Require Import core fintype owl constants.

Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.
From Coq Require Import Arith.Arith.

(* l for label variables in scope *)
(* d for type variables in scope  *)
(* m for term variables in scope  *)

(* adversary is always the first variable in scope *)
Definition adv : (label 1) := (var_label var_zero).

Definition gamma_context (l : nat) (d : nat) (m : nat) := fin m -> ty l d.

Definition delta_context (l : nat) (d : nat) := fin d -> ty l d.

Definition phi_context (l : nat) := (list (constr l)).

Definition lift_delta {l : nat} {d : nat} (Delta : fin (S d) -> ty l d)
  : delta_context l (S d)
  := fun i => ren_ty id shift (Delta i).

Inductive is_value { l m } : tm l m -> Prop :=
| error_value : is_value error
| skip_value : is_value skip
| loc_value : forall n,
  is_value (loc n)
| bitstring_value : forall b,
  is_value (bitstring b)
| fixlam_value : forall e,
  is_value (fixlam e)
| pair_value : forall v1 v2,
  is_value v1 ->
  is_value v2 ->
  is_value (tm_pair v1 v2)
| inl_value : forall v,
  is_value v ->
  is_value (inl v)
| inr_value : forall v,
  is_value v ->
  is_value (inr v)
| tlam_value : forall e,
  is_value (tlam e)
| l_lam_value : forall e,
  is_value (l_lam e)
| pack_value : forall v,
  is_value v ->
  is_value (pack v).

Inductive Kctx {l m : nat} :=
| KHole : Kctx
| ZeroK : Kctx -> Kctx
| KAppL : Kctx -> tm l m -> Kctx
| KAppR : forall (v : tm l m), is_value v -> Kctx -> Kctx
| KAlloc : Kctx -> Kctx
| KDeAlloc : Kctx -> Kctx
| KAssignL : Kctx -> tm l m -> Kctx
| KAssignR : forall (v : tm l m), is_value v -> Kctx -> Kctx
| KPairL : Kctx -> tm l m -> Kctx
| KPairR : forall (v : tm l m), is_value v -> Kctx -> Kctx
| KFst : Kctx -> Kctx
| KSnd : Kctx -> Kctx
| KInl : Kctx -> Kctx
| KInR : Kctx -> Kctx
| KCase : Kctx -> tm l (S m) -> tm l (S m) -> Kctx
| KTapp : Kctx -> Kctx
| KLapp : Kctx -> label l -> Kctx
| KPack : Kctx -> Kctx
| KUnpack : Kctx -> tm l (S m) -> Kctx
| KIf : Kctx -> tm l m -> tm l m -> Kctx
| KSync : Kctx -> Kctx.

Fixpoint Plug (K : Kctx) (t : tm 0 0) : (tm 0 0) :=
   match K with
   | KHole => t 
   | ZeroK K' => zero (Plug K' t)
   | KAppL K' e => (Core.app (Plug K' t) e)
   | KAppR  v _ K' => (Core.app v (Plug K' t))
   | KAlloc K' => (alloc (Plug K' t))
   | KDeAlloc K' => (dealloc (Plug K' t))
   | KAssignL K' e => (assign (Plug K' t) e)
   | KAssignR  v _ K' => (assign v (Plug K' t))
   | KPairL K' e => (tm_pair (Plug K' t) e)
   | KPairR  v _ K' => (tm_pair v (Plug K' t))
   | KFst K' => (left_tm (Plug K' t))
   | KSnd K' => (right_tm (Plug K' t))
   | KInl K' => (inl (Plug K' t))
   | KInR  K' => (inr (Plug K' t))
   | KCase K' e1 e2 => (case (Plug K' t) e1 e2)
   | KTapp K' => (tapp (Plug K' t))
   | KLapp  K' l => (lapp (Plug K' t) l)
   | KPack  K' => (pack (Plug K' t))
   | KUnpack  K' e => (unpack (Plug K' t) e)
   | KIf K' e1 e2 => (if_tm (Plug K' t) e1 e2)
   | KSync K' => (sync (Plug K' t))
   end.

Fixpoint generate_zero (b : binary) : binary :=
  match b with
  | (bone b') => (bzero (generate_zero b'))
  | (bzero b') => (bzero (generate_zero b'))
  | bend => bend 
  end.

Fixpoint all_zero (b : binary) : Prop :=
  match b with
  | (bone b') => False
  | (bzero b') => (all_zero b')
  | bend => True 
  end.

Definition mem (l m : nat) := nat -> option (tm l m).

Definition only_values {l m} (memory : mem l m) : Prop :=
  forall a t, memory a = Some t -> is_value t.

Definition test_mem (l m : nat) : mem l m :=
  fun i =>
    match i with 
    | 0 => Some (zero error)
    | (S _) => None
    end.

Definition allocate {l m} (location : nat) (v : tm l m) (memory : mem l m) : (mem l m) :=
  fun i =>
    if (Nat.eq_dec i location)
    then Some v
    else memory i.

Parameter fresh : forall {l m}, mem l m -> nat.

Axiom fresh_not_allocated :
  forall {l m} (memory : mem l m), memory (fresh memory) = None.

(* Convert from labels down to lattice elements *)
Fixpoint interp_lattice (l : label 0) : L.(labels) :=
  match l with 
  | latl x => x
  | ljoin x y => (L.(join) (interp_lattice x) (interp_lattice y)) 
  | lmeet x y => (L.(meet) (interp_lattice x) (interp_lattice y)) 
  | var_label n => match n with end
  end.

(* Simple Negation method *)
Definition negate_cond {l} (co : constr l) : constr l :=
  match co with
  | (condition Core.leq x y) => (condition nleq x y)
  | (condition geq x y) => (condition ngeq x y)
  | (condition gt x y) => (condition ngt x y)
  | (condition lt x y) => (condition nlt x y)
  | (condition nleq x y) => (condition Core.leq x y)
  | (condition ngeq x y) => (condition geq x y)
  | (condition ngt x y) => (condition gt x y)
  | (condition nlt x y) => (condition lt x y)
  end.  

(* Check if a constraint is valid, under the assumption it is closed *)
Definition valid_constraint (co : constr 0) : Prop :=
  match co with
  | (condition Core.leq x y) => L.(leq) (interp_lattice x) (interp_lattice y) = true
  | (condition geq x y) => L.(leq) (interp_lattice y) (interp_lattice x) = true
  | (condition gt x y) => L.(leq) (interp_lattice y) (interp_lattice x) = true /\ L.(leq) (interp_lattice x) (interp_lattice y) = false
  | (condition lt x y) => L.(leq) (interp_lattice x) (interp_lattice y) = true /\ L.(leq) (interp_lattice y) (interp_lattice x) = false
  | (condition nleq x y) => L.(leq) (interp_lattice y) (interp_lattice x) = false
  | (condition ngeq x y) => L.(leq) (interp_lattice y) (interp_lattice x) = false
  | (condition ngt x y) => L.(leq) (interp_lattice y) (interp_lattice x) = false \/ L.(leq) (interp_lattice x) (interp_lattice y) = true
  | (condition nlt x y) => L.(leq) (interp_lattice x) (interp_lattice y) = false \/ L.(leq) (interp_lattice y) (interp_lattice x) = false
  end.

(* General logic for non error reductions, and how they function *)
Inductive reduction : (tm 0 0 * mem 0 0) -> (tm 0 0 * mem 0 0) -> Prop := 
| r_zero : forall b memory, 
  reduction (zero (bitstring b), memory) ((bitstring (generate_zero b)), memory)
| r_ift : forall b e1 e2 memory, 
  all_zero b -> 
  reduction (if_tm (bitstring b) e1 e2, memory) (e1, memory)
| r_iff : forall b e1 e2 memory, 
  (not (all_zero b)) -> 
  reduction (if_tm (bitstring b) e1 e2, memory) (e2, memory)
| r_alloc : forall v memory,
  is_value v ->
  let res := (fresh memory) in
  reduction (alloc v, memory) (loc res, (allocate res v memory))
| r_deref : forall n memory v,
  memory n = Some v ->
  reduction (dealloc (loc n), memory) (v, memory)
| r_assign : forall n v memory,
  is_value v ->
  reduction (assign (loc n) v, memory) (skip, (allocate n v memory))
| r_fix : forall e v memory,
  is_value v ->
  reduction (Core.app (fixlam e) v, memory) ((subst_tm var_label (scons v (scons (fixlam e) var_tm)) e), memory)
| r_pair_l : forall v1 v2 memory,
  is_value v1 ->
  is_value v2 ->
  reduction (left_tm (tm_pair v1 v2), memory) (v1, memory)
| r_pair_r : forall v1 v2 memory,
  is_value v1 ->
  is_value v2 ->
  reduction (right_tm (tm_pair v1 v2), memory) (v2, memory)
| r_case_l : forall v e1 e2 memory,
  is_value v ->
  reduction (case (inl v) e1 e2, memory) (subst_tm var_label(scons v var_tm) e1, memory)
| r_case_r : forall v e1 e2 memory,
  is_value v ->
  reduction (case (inr v) e1 e2, memory) (subst_tm var_label (scons v var_tm) e2, memory)
| r_tapp : forall e memory,
  reduction (tapp (tlam e), memory) (e, memory)
| r_lapp : forall e lab memory,
  reduction (lapp (l_lam e) lab, memory) ((subst_tm (scons lab var_label) var_tm e), memory)
| r_unpack : forall v e memory,
  is_value v ->
  reduction (unpack (pack v) e, memory) (subst_tm var_label (scons v var_tm) e, memory)
| r_iflt : forall c e1 e2 memory,
  valid_constraint c ->
  reduction (if_c c e1 e2, memory) (e1, memory)
| r_iflf : forall c e1 e2 memory,
  not (valid_constraint c) ->
  reduction (if_c c e1 e2, memory) (e2, memory).

(* To check if an evaluation is unable to continue/is malformed *)
Definition stuck (v : tm 0 0) (memory : mem 0 0) :=
  not (is_value v) /\
      (forall v' memory',
        not (reduction (v, memory) (v', memory'))).

(* General logic for evaluating a term down: create a context and evaluate it *)
Inductive step : (tm 0 0 * mem 0 0) -> (tm 0 0 * mem 0 0) -> Prop :=
| step_ctx : forall K e memory e' memory',
  reduction (e, memory) (e', memory') ->
  step (Plug K e, memory) (Plug K e', memory')
| step_error : forall v memory,
  stuck v memory ->
  step (v, memory) (error, memory).

Lemma test_step :
  forall (memory : mem 0 0),
    step ((zero (bitstring (bone (bone bend)))), memory) ((bitstring (bzero (bzero bend))), memory).
Proof.
  intros.
  Check zero (bitstring (bone (bone bend))).
  assert ((Plug KHole (zero (bitstring (bone (bone bend))))) = (zero (bitstring (bone (bone bend))))) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht.
  specialize (step_ctx KHole (zero (bitstring (bone (bone bend)))) memory (bitstring (bzero (bzero bend))) memory) as Hn.
  specialize (r_zero (bone (bone bend)) memory) as Hx. simpl in Hx.
  specialize (Hn Hx).
  assumption.
Qed.

Lemma test_error :
  forall (memory : mem 0 0),
    step (zero skip, memory) (error, memory).
Proof.
  intros.
  specialize (step_error (zero skip) memory) as Hx.
  assert (stuck (zero skip) memory) as Hs. {
    unfold stuck.
    split.
    - intros H. inversion H.
    - intros. intro H. inversion H. 
  }
  specialize (Hx Hs).
  assumption.
Qed.

(* Complete subtyping next, minus the material about ops... probablity later *)

(* Missing ST_VAR ST_DATA ST_LATUNIV And the other label defs... *)

Inductive subtype {l d} (Phi : phi_context l) (Delta : delta_context l d) :
  ty l d -> ty l d -> Prop :=
| ST_Any : forall t,
  subtype Phi Delta t Any
| ST_Unit : subtype Phi Delta Unit Unit
| ST_Func : forall t1' t1 t2 t2',
  subtype Phi Delta t1' t1 ->
  subtype Phi Delta t2 t2' ->
  subtype Phi Delta (arr t1 t2) (arr t1' t2')
| ST_Prod : forall t1 t1' t2 t2',
  subtype Phi Delta t1 t1' ->
  subtype Phi Delta t2 t2' ->
  subtype Phi Delta (prod t1 t2) (prod t1' t2')
| ST_Sum : forall t1 t1' t2 t2',
  subtype Phi Delta t1 t1' ->
  subtype Phi Delta t2 t2' ->
  subtype Phi Delta (sum t1 t2) (sum t1' t2')
| ST_Ref : forall t,
  subtype Phi Delta (Ref t) (Ref t)
| ST_Univ : forall t0 t0' t t',
  subtype Phi Delta t0 t0' ->
  subtype Phi (lift_delta (scons t0' Delta)) t t' ->
  subtype Phi Delta (all t0 t) (all t0' t')
| ST_Exist : forall t0 t0' t t',
  subtype Phi Delta t0 t0' ->
  subtype Phi (lift_delta (scons t0 Delta)) t t' ->
  subtype Phi Delta (ex t0 t) (ex t0' t').
