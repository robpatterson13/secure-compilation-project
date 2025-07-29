Require Import core fintype owl.

Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.
From Coq Require Import Arith.Arith.

Record Lattice := {
  labels : Set;
}.

Record Ops := {
  operations : Set;
}.

Inductive fooset : Set :=
| foo1
| bar1
| baz1.

Inductive fooset2 : Set :=
| foo2
| bar2
| baz2.

Definition fooimpl : Lattice := {| labels := fooset |}.
Definition fooimpl2 : Lattice := {| labels := fooset2 |}.

Inductive test : forall L, L.(labels) -> Prop :=
| tester : forall L a,
  test L a.

Lemma test_without_var :
  test fooimpl foo1.
Proof.
constructor.
Qed.

(* Testing out records *)
Section FooWorld.

  Variable L : Lattice.

  Inductive footype : Type :=
  | footm : L.(labels) -> footype.

  Inductive evalfoo : footype -> nat -> Prop :=
  | foobasic : forall a,
    evalfoo (footm a) 10.

  Inductive test_sec : L.(labels) -> Prop :=
  | tester_sec : forall a,
    test_sec a.

End FooWorld.

Check evalfoo.

(* Testing out using records and variables *)

Lemma test_with_var :
  test_sec fooimpl foo1.
Proof.
constructor.
Qed.

Lemma test_eval :
  evalfoo fooimpl (footm fooimpl foo1) 10.
Proof.
  constructor.
Qed.

Lemma test_eval2 :
  evalfoo fooimpl2 (footm fooimpl2 foo2) 10.
Proof.
  constructor.
Qed.

(* End of testing, resume impl *)

Section OwlWorld.

Variable L : Lattice.

(* l for label variables in scope *)
(* d for type variables in scope  *)
(* m for term variables in scope  *)


Definition gamma_context (l : nat) (d : nat) (m : nat) := fin m -> ty l d.

Definition delta_context (l : nat) (d : nat) := fin d -> ty l d.

Definition phi_context (l : nat) := (list (constr l)).

Definition lift_delta {l : nat} {d : nat} (Delta : fin (S d) -> ty l d)
  : delta_context l (S d)
  := fun i => ren_ty id shift (Delta i).

Inductive is_value { l d m } : tm l d m -> Prop :=
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

Inductive Kctx (l d m : nat) :=
| KHole : Kctx l d m
| ZeroK : Kctx l d m -> Kctx l d m
| KAppL : Kctx l d m -> tm l d m -> Kctx l d m
| KAppR : forall (v : tm l d m), is_value v -> Kctx l d m -> Kctx l d m
| KAlloc : Kctx l d m -> Kctx l d m
| KDeAlloc : Kctx l d m -> Kctx l d m
| KAssignL : Kctx l d m -> tm l d m -> Kctx l d m
| KAssignR : forall (v : tm l d m), is_value v -> Kctx l d m -> Kctx l d m
| KPairL : Kctx l d m -> tm l d m -> Kctx l d m
| KPairR : forall (v : tm l d m), is_value v -> Kctx l d m -> Kctx l d m
| KFst : Kctx l d m -> Kctx l d m
| KSnd : Kctx l d m -> Kctx l d m
| KInl : Kctx l d m -> Kctx l d m
| KInR : Kctx l d m -> Kctx l d m
| KCase : Kctx l d m -> tm l d (S m) -> tm l d (S m) -> Kctx l d m
| KTapp : Kctx l d m -> ty l d -> Kctx l d m
| KLapp : Kctx l d m -> label l -> Kctx l d m
| KPack : Kctx l d m -> Kctx l d m
| KUnpack : Kctx l d m -> tm l d (S m) -> Kctx l d m
| KIf : Kctx l d m -> tm l d m -> tm l d m -> Kctx l d m
| KSync : Kctx l d m -> Kctx l d m.

Fixpoint Plug { l d m : nat } (K : Kctx l d m) (t : tm l d m) : (tm l d m) :=
   match K with
   | KHole _ _ _ => t 
   | ZeroK _ _ _ K' => zero (Plug K' t)
   | KAppL _ _ _ K' e => (Core.app (Plug K' t) e)
   | KAppR _ _ _ v _ K' => (Core.app v (Plug K' t))
   | KAlloc _ _ _ K' => (alloc (Plug K' t))
   | KDeAlloc _ _ _ K' => (dealloc (Plug K' t))
   | KAssignL _ _ _ K' e => (assign (Plug K' t) e)
   | KAssignR _ _ _ v _ K' => (assign v (Plug K' t))
   | KPairL _ _ _ K' e => (tm_pair (Plug K' t) e)
   | KPairR _ _ _ v _ K' => (tm_pair v (Plug K' t))
   | KFst _ _ _ K' => (left_tm (Plug K' t))
   | KSnd _ _ _ K' => (right_tm (Plug K' t))
   | KInl _ _ _ K' => (inl (Plug K' t))
   | KInR _ _ _ K' => (inr (Plug K' t))
   | KCase _ _ _ K' e1 e2 => (case (Plug K' t) e1 e2)
   | KTapp _ _ _ K' t' => (tapp (Plug K' t) t')
   | KLapp _ _ _ K' l => (lapp (Plug K' t) l)
   | KPack _ _ _ K' => (pack (Plug K' t))
   | KUnpack _ _ _ K' e => (unpack (Plug K' t) e)
   | KIf _ _ _ K' e1 e2 => (if_tm (Plug K' t) e1 e2)
   | KSync _ _ _ K' => (sync (Plug K' t))
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

Definition mem (l d m : nat) := nat -> option (tm l d m).

Definition only_values {l d m} (memory : mem l d m) : Prop :=
  forall a t, memory a = Some t -> is_value t.

Definition test_mem (l d m : nat) : mem l d m :=
  fun i =>
    match i with 
    | 0 => Some (zero error)
    | (S _) => None
    end.

Definition allocate {l d m} (location : nat) (v : tm l d m) (memory : mem l d m) : (mem l d m) :=
  fun i =>
    if (Nat.eq_dec i location)
    then Some v
    else memory i.

Parameter fresh : forall {l d m}, mem l d m -> nat.

Parameter valid_constraint : forall {l}, constr l -> Prop.

Axiom fresh_not_allocated :
  forall {l d m} (memory : mem l d m), memory (fresh memory) = None.

(* General logic for non error reductions, and how they function *)
Inductive reduction {l d m : nat} : (tm l d m * mem l d m) -> (tm l d m * mem l d m) -> Prop := 
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
  reduction (Core.app (fixlam e) v, memory) ((subst_tm var_label var_ty (scons v (scons (fixlam e) var_tm)) e), memory)
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
  reduction (case (inl v) e1 e2, memory) (subst_tm var_label var_ty (scons v var_tm) e1, memory)
| r_case_r : forall v e1 e2 memory,
  is_value v ->
  reduction (case (inr v) e1 e2, memory) (subst_tm var_label var_ty (scons v var_tm) e2, memory)
| r_tapp : forall e t memory,
  reduction (tapp (tlam e) t, memory) (subst_tm var_label (scons t var_ty) var_tm e, memory)
| r_lapp : forall e lab memory,
  reduction (lapp (l_lam e) lab, memory) ((subst_tm (scons lab var_label) var_ty var_tm e), memory)
| r_unpack : forall v e memory,
  is_value v ->
  reduction (unpack (pack v) e, memory) (subst_tm var_label var_ty (scons v var_tm) e, memory)
| r_iflt : forall c e1 e2 memory,
  valid_constraint c ->
  reduction (if_c c e1 e2, memory) (e1, memory)
| r_iflf : forall c e1 e2 memory,
  not (valid_constraint c) ->
  reduction (if_c c e1 e2, memory) (e2, memory).

(* To check if an evaluation is unable to continue/is malformed *)
Definition stuck { l d m } (v : tm l d m) (memory : mem l d m) :=
  not (is_value v) /\
      (forall v' memory',
        not (reduction (v, memory) (v', memory'))).

(* General logic for evaluating a term down: create a context and evaluate it *)
Inductive step { l d m : nat } : (tm l d m * mem l d m) -> (tm l d m * mem l d m) -> Prop :=
| step_ctx : forall K e memory e' memory',
  reduction (e, memory) (e', memory') ->
  step (Plug K e, memory) (Plug K e', memory')
| step_error : forall v memory,
  stuck v memory ->
  step (v, memory) (error, memory).

Lemma test_step :
  forall (memory : mem 0 0 0),
    step ((zero (bitstring (bone (bone bend)))), memory) ((bitstring (bzero (bzero bend))), memory).
Proof.
  intros.
  Check zero (bitstring (bone (bone bend))).
  assert ((Plug (KHole 0 0 0) (zero (bitstring (bone (bone bend))))) = (zero (bitstring (bone (bone bend))))) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht.
  specialize (step_ctx (KHole 0 0 0) (zero (bitstring (bone (bone bend)))) memory (bitstring (bzero (bzero bend))) memory) as Hn.
  specialize (r_zero (bone (bone bend)) memory) as Hx. simpl in Hx.
  specialize (Hn Hx).
  assumption.
Qed.

Lemma test_error :
  forall (memory : mem 0 0 0),
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

End OwlWorld.
