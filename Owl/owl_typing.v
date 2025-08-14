Require Import core fintype owl constants Dist.

Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.
From Coq Require Import Arith.Arith.

(* l for label variables in scope *)
(* d for type variables in scope  *)
(* m for term variables in scope  *)

(* Example: *)

Axiom foo : list nat -> Dist nat.
Check (x <- foo (1 :: 2 :: 3 :: nil);; ret (x + 1)).

(* Non-probability stuff *)

Definition gamma_context (l : nat) (d : nat) (m : nat) := fin m -> ty l d.

Definition delta_context (l : nat) (d : nat) := fin d -> ty l d.

Definition phi_context (l : nat) := (list (constr l)).

Definition empty_gamma {l d} : gamma_context l d 0 :=
  fun (i : fin 0) => match i with end.

Definition empty_delta {l} : delta_context l 0 :=
  fun (i : fin 0) => match i with end.

Definition empty_phi {l} : (phi_context l) := [].

Definition lift_delta {l : nat} {d : nat} (Delta : fin (S d) -> ty l d)
  : delta_context l (S d)
  := fun i => ren_ty id shift (Delta i).

Definition lift_delta_l {l : nat} {d : nat} (Delta : delta_context l d)
  : delta_context (S l) d
  := fun i => ren_ty shift id (Delta i).

Definition lift_gamma {l d m} (Gamma : gamma_context l d m)
  : gamma_context l (S d) m
  := fun i => ren_ty id shift (Gamma i).

Definition lift_gamma_l {l d m} (Gamma : gamma_context l d m)
  : gamma_context (S l) d m
  := fun i => ren_ty shift id (Gamma i).


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

Definition phi_map (l : nat) : Type := (fin l) -> (label 0).

Definition phi_map_holds (l : nat) (pm : phi_map l) (co : constr l) : Prop := 
  match co with
  | (condition c l1 l2) => (valid_constraint (condition c (subst_label pm l1) (subst_label pm l2)))
  end.

Definition lift_phi {l} (pm : phi_context l) : phi_context (S l) :=
  map (ren_constr shift) pm.

Inductive valid_phi_map : forall l, phi_map l -> phi_context l -> Prop :=
| phi_empty_valid : forall (pm : phi_map 1),
  valid_phi_map 1 pm empty_phi 
| phi_constraint_valid : forall l pm phictx c,
  valid_phi_map l pm phictx ->
  phi_map_holds l pm c ->
  valid_phi_map l pm (c :: phictx)
| phi_var_holds : forall l lab pm phictx,
  valid_phi_map l pm phictx ->
  valid_phi_map (S l) (scons lab pm) (lift_phi phictx).

Definition phi_entails_c {l} (pctx : phi_context l) (co : constr l) : Prop :=
  (forall pm,
    valid_phi_map l pm pctx ->
    phi_map_holds l pm co).

Notation "pctx |= co" := (phi_entails_c pctx co)
  (at level 100, right associativity).

Notation "! e" := (dealloc e)
  (at level 100, right associativity).

(* Checks for proper values within terms *)
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

Inductive is_redex { l m } : tm l m -> Prop :=
| zero_redex : forall v,
  is_value v ->
  is_redex (zero v).

(* K context (continuance) for evaluation rules *)
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

(* Plug a term into the expression context K to get a resulting term *)
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

(* generate a bitstring of the form {0}* *)
Fixpoint generate_zero (b : binary) : binary :=
  match b with
  | (bone b') => (bzero (generate_zero b'))
  | (bzero b') => (bzero (generate_zero b'))
  | bend => bend 
  end.

(* check if a bitstring is all 0s *)
Fixpoint all_zero (b : binary) : Prop :=
  match b with
  | (bone b') => False
  | (bzero b') => (all_zero b')
  | bend => True 
  end.

Definition mem (l m : nat) := nat -> option (tm l m).

(* Memory only contains value terms *)
Definition only_values {l m} (memory : mem l m) : Prop :=
  forall a t, memory a = Some t -> is_value t.

Definition test_mem (l m : nat) : mem l m :=
  fun i =>
    match i with 
    | 0 => Some (zero error)
    | (S _) => None
    end.

(* Allocate a new area of memory at a specified location *)
Definition allocate {l m} (location : nat) (v : tm l m) (memory : mem l m) : (mem l m) :=
  fun i =>
    if (Nat.eq_dec i location)
    then Some v
    else memory i.

Parameter fresh : forall {l m}, mem l m -> nat.

Definition convert_to_bitstring (l d : nat) (bs : binary) : tm l d :=
   (bitstring bs).

Axiom fresh_not_allocated :
  forall {l m} (memory : mem l m), memory (fresh memory) = None.

(* General logic for non error reductions, and how they function *)
Inductive tm_reduction : (tm 0 0 * mem 0 0 * binary) -> Dist (tm 0 0 * mem 0 0 * binary) -> Prop := 
| r_zero : forall b memory s, 
  tm_reduction (zero (bitstring b), memory, s) (Ret ((bitstring (generate_zero b)), memory, s))
| r_ift : forall b e1 e2 memory s, 
  all_zero b -> 
  tm_reduction (if_tm (bitstring b) e1 e2, memory, s) (Ret (e1, memory, s))
| r_iff : forall b e1 e2 memory s, 
  (not (all_zero b)) -> 
  tm_reduction (if_tm (bitstring b) e1 e2, memory, s) (Ret (e2, memory, s))
| r_alloc : forall v memory s,
  is_value v ->
  let res := (fresh memory) in
  tm_reduction (alloc v, memory, s) (Ret (loc res, (allocate res v memory), s))
| r_deref : forall n memory v s,
  memory n = Some v ->
  tm_reduction (dealloc (loc n), memory, s) (Ret (v, memory, s))
| r_assign : forall n v memory s,
  is_value v ->
  tm_reduction (assign (loc n) v, memory, s) (Ret (skip, (allocate n v memory), s))
| r_fix : forall e v memory s,
  is_value v ->
  tm_reduction (Core.app (fixlam e) v, memory, s) (Ret ((subst_tm var_label (scons v (scons (fixlam e) var_tm)) e), memory, s))
| r_pair_l : forall v1 v2 memory s,
  is_value v1 ->
  is_value v2 ->
  tm_reduction (left_tm (tm_pair v1 v2), memory, s) (Ret (v1, memory, s))
| r_pair_r : forall v1 v2 memory s,
  is_value v1 ->
  is_value v2 ->
  tm_reduction (right_tm (tm_pair v1 v2), memory, s) (Ret (v2, memory, s))
| r_case_l : forall v e1 e2 memory s,
  is_value v ->
  tm_reduction (case (inl v) e1 e2, memory, s) (Ret (subst_tm var_label(scons v var_tm) e1, memory, s))
| r_case_r : forall v e1 e2 memory s,
  is_value v ->
  tm_reduction (case (inr v) e1 e2, memory, s) (Ret (subst_tm var_label (scons v var_tm) e2, memory, s))
| r_tapp : forall e memory s,
  tm_reduction (tapp (tlam e), memory, s) (Ret (e, memory, s))
| r_lapp : forall e lab memory s,
  tm_reduction (lapp (l_lam e) lab, memory, s) (Ret ((subst_tm (scons lab var_label) var_tm e), memory, s))
| r_unpack : forall v e memory s,
  is_value v ->
  tm_reduction (unpack (pack v) e, memory, s) (Ret (subst_tm var_label (scons v var_tm) e, memory, s))
| r_iflt : forall c e1 e2 memory s,
  valid_constraint c ->
  tm_reduction (if_c c e1 e2, memory, s) (Ret (e1, memory, s))
| r_iflf : forall c e1 e2 memory s,
  not (valid_constraint c) ->
  tm_reduction (if_c c e1 e2, memory, s) (Ret (e2, memory, s))
| r_op : forall f es bs memory s,
  es = (map (convert_to_bitstring 0 0) bs) ->
  tm_reduction ((Op f es), memory, s) (b <- (f bs);; (Ret (bitstring b, memory, s))).

Check tm_reduction.

(* To check if an evaluation is unable to continue/is malformed *)
Definition stuck (v : tm 0 0) (memory : mem 0 0) (s : binary) :=
  not (is_value v) /\
      (forall (D : (Dist (tm 0 0 * mem 0 0 * binary))),
        not (tm_reduction (v, memory, s) D)).

(* Integrate stuck as a reducible result *)
Inductive reduce : (tm 0 0 * mem 0 0 * binary) -> Dist (tm 0 0 * mem 0 0 * binary) -> Prop := 
| reduce_tm : forall A B,
  tm_reduction A B ->
  reduce A B
| reduce_stuck : forall v memory s,
  stuck v memory s ->
  reduce (v, memory, s) (Ret (error, memory, s)).

Definition plug_dist (K : Kctx) (c : (tm 0 0 * mem 0 0 * binary)) : (tm 0 0 * mem 0 0 * binary) :=
  let '(e,m,s) := c in (Plug K e, m, s).
  
(* General logic for evaluating a term down/performing steps of an execution *)
Inductive exec : nat -> (tm 0 0 * mem 0 0 * binary) -> Dist (tm 0 0 * mem 0 0 * binary) -> Prop :=
| exec_return : forall k e m s,
  is_value e \/ k = 0 ->
  exec k (e, m, s) (ret (e, m, s))
| exec_step : forall k K r m s D R,
  reduce (r, m, s) D ->
  exec_dist k K D R ->
  exec (S k) (Plug K r, m, s) R
with exec_dist : nat -> Kctx -> Dist (tm 0 0 * mem 0 0 * binary) -> Dist (tm 0 0 * mem 0 0 * binary) -> Prop :=
| exec_dist_ret : forall k K c R,
  exec k (plug_dist K c) R ->
  exec_dist k K (Ret c) R
| exec_dist_flip : forall k K f R,
  (forall b, exec_dist k K (f b) (R b)) ->
  exec_dist k K (Flip f) (Flip R).  

(* Test step/execute lemmas to see if we're in the correct place *)
Lemma test_exec :
  forall (memory : mem 0 0) s,
    exec 10 ((zero (bitstring (bone (bone bend)))), memory, s) (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  Check zero (bitstring (bone (bone bend))).
  assert ((Plug KHole (zero (bitstring (bone (bone bend))))) = (zero (bitstring (bone (bone bend))))) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht.
  specialize (exec_step 9 KHole (zero (bitstring (bone (bone bend)))) memory s (ret ((bitstring (bzero (bzero bend))), memory, s))) as Hn.
  simpl in Hn.
  specialize (Hn (ret ((bitstring (bzero (bzero bend))), memory, s))).
  simpl in Hn.
  specialize (r_zero (bone (bone bend)) memory s) as Hx. simpl in Hx.
  specialize (reduce_tm (zero (bitstring (bone (bone bend))), memory, s) (ret (bitstring (bzero (bzero bend)), memory, s)) Hx) as Hr.
  specialize (Hn Hr). simpl.
  apply Hn.
  constructor. 
  simpl.
  constructor. 
  left.
  constructor.
Qed.

Lemma test_exec_2 :
  forall (memory : mem 0 0) s,
    exec 10 ((zero (zero (bitstring (bone (bone bend))))), memory, s) (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  assert ((Plug (ZeroK KHole) (zero (bitstring (bone (bone bend))))) = (zero (zero (bitstring (bone (bone bend)))))) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht. specialize (exec_step 9 (ZeroK KHole) (zero (bitstring (bone (bone bend)))) memory s (ret ((bitstring (bzero (bzero bend))), memory, s)) (ret ((bitstring (bzero (bzero bend))), memory, s))) as Hes.
  simpl in Hes.
  specialize (r_zero (bone (bone bend)) memory s) as Hx.
  specialize (reduce_tm (zero (bitstring (bone (bone bend))), memory, s) (ret(bitstring (bzero (bzero bend)), memory, s))) as Hr.
  specialize (Hr Hx).
  specialize (Hes Hr).
  simpl.
  apply Hes.
  constructor.
  simpl.
  clear Hr Hx Hes Ht. 
  assert ((Plug KHole (zero (bitstring (bzero (bzero bend))))) = (zero (bitstring (bzero (bzero bend))))) as Ht. {
    simpl. reflexivity.
  }
  specialize (exec_step 8 KHole (zero (bitstring (bzero (bzero bend)))) memory s (ret ((bitstring (bzero (bzero bend))), memory, s))) as Hs.
  specialize (Hs (ret ((bitstring (bzero (bzero bend))), memory, s))).
  specialize (r_zero (bzero (bzero bend)) memory s) as Hz.
  specialize (reduce_tm (zero (bitstring (bzero (bzero bend))), memory, s) (ret (bitstring (generate_zero (bzero (bzero bend))), memory, s)) Hz) as Hr.
  specialize (Hs Hr). 
  apply Hs.
  constructor.
  simpl.
  constructor.
  left.
  constructor.
Qed.
  
Lemma test_error :
  forall (memory : mem 0 0) s,
    exec 5 (zero skip, memory, s) (ret (error, memory, s)).
Proof.
  intros.
  assert (stuck (zero skip) memory s) as Hs. {
    unfold stuck.
    split.
    - intros H. inversion H.
    - intros. intro H. inversion H. 
  }
  specialize (reduce_stuck (zero skip) memory s Hs) as Hr.
  specialize (exec_step 4 KHole (zero skip) memory s (ret (error, memory, s))) as Hx.
  simpl in Hx.
  specialize (Hx (ret (error, memory, s))). simpl in Hx.
  specialize (Hx Hr).
  apply Hx.
  constructor.
  simpl.
  constructor.
  left.
  constructor.
Qed.

(* Complete subtyping next, minus the material about ops... probablity later or maybe right now *)

(* subtyping rules for Owl *)
Inductive subtype {l d} (Phi : phi_context l) (Delta : delta_context l d) :
  ty l d -> ty l d -> Prop :=
| ST_Var : forall x t',
  subtype Phi Delta (Delta x) t' ->
  subtype Phi Delta (var_ty x) t'
| ST_Any : forall t,
  subtype Phi Delta t Any
| ST_Unit : subtype Phi Delta Unit Unit
| ST_Data : forall lab lab',
  (Phi |= (condition Core.leq lab lab')) ->
  subtype Phi Delta (Data lab) (Data lab')
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
  subtype Phi Delta (ex t0 t) (ex t0' t')
| ST_LatUniv : forall cs (lab : label l) (lab' : label l) t t',
  (((condition cs (var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi)) 
  |= (condition cs (var_label var_zero) (ren_label shift lab'))) ->
  subtype ((condition cs (var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi)) (lift_delta_l Delta) t t' ->
  subtype Phi Delta (all_l cs lab t) (all_l cs lab' t')
| ST_IfElimL : forall co t1 t2 t1',
  (Phi |= co) -> 
  subtype Phi Delta t1 t1' ->
  subtype Phi Delta (t_if co t1 t2) t1'
| ST_IfElimR : forall co t1 t2 t2',
  (Phi |= (negate_cond co)) -> 
  subtype Phi Delta t2 t2' ->
  subtype Phi Delta (t_if co t1 t2) t2'
| ST_IfIntroL : forall co t1 t1' t2',
  (Phi |= co) ->
  subtype Phi Delta t1 t1' ->
  subtype Phi Delta t1 (t_if co t1' t2')
| ST_IfIntroR : forall co t2 t1' t2',
  (Phi |= (negate_cond co)) ->
  subtype Phi Delta t2 t2' ->
  subtype Phi Delta t2 (t_if co t1' t2')
| ST_Lem : forall co t t',
  subtype (co :: Phi) Delta t t' ->
  subtype ((negate_cond co) :: Phi) Delta t t' ->
  subtype Phi Delta t t'.

Fixpoint last_var l : fin (S l) :=
  match l with
  | 0   => None
  | S n => Some (last_var n) 
  end.

Require Import Lia.

(* The adversary is the first defined, and therefore last variable, in scope *)
Definition adv {l : nat} (pf : l > 0) : label l.
Proof.
  destruct l.
  - lia. 
  - exact (var_label (last_var l)).
Defined.

Lemma three_proof : 
  3 > 0.
Proof.
lia.
Qed.

Transparent adv.
Compute (adv three_proof).

(* Typing rules for Owl *)
Inductive has_type {l d m : nat} (Phi : phi_context l) (Delta : delta_context l d) (Gamma : gamma_context l d m) :
  tm l m -> ty l d -> Prop :=
| T_Var : forall x,
  has_type Phi Delta Gamma (var_tm x) (Gamma x)
| T_IUnit : has_type Phi Delta Gamma skip Unit
| T_Const : forall b,
  has_type Phi Delta Gamma (bitstring b) (Data (latl L.(bot)))
| T_Zero : forall e l,
  has_type Phi Delta Gamma e (Data l) ->
  has_type Phi Delta Gamma (zero e) (Data (latl (L.(bot))))
| T_If : forall e e1 e2 t,
  has_type Phi Delta Gamma e (Data (latl L.(bot))) ->
  has_type Phi Delta Gamma e1 t ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (if_tm e e1 e2) t
| T_IRef : forall e t,
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma (alloc e) (Ref t)
| T_ERef : forall e t,
  has_type Phi Delta Gamma e (Ref t) ->
  has_type Phi Delta Gamma (! e) t
| T_Assign : forall e1 e2 t,
  has_type Phi Delta Gamma e1 (Ref t) ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (assign e1 e2) Unit
| T_IFun : forall e t t',
  has_type Phi Delta (scons t (scons (arr t t') Gamma)) e t ->
  has_type Phi Delta Gamma (fixlam e) (arr t t')
| T_EFun : forall e1 e2 t t',
  has_type Phi Delta Gamma e1 (arr t t') ->
  has_type Phi Delta Gamma e2 t ->
  has_type Phi Delta Gamma (Core.app e1 e2) t
| T_IProd : forall e1 e2 t1 t2,
  has_type Phi Delta Gamma e1 t1 ->
  has_type Phi Delta Gamma e2 t2 ->
  has_type Phi Delta Gamma (tm_pair e1 e2) (prod t1 t2)
| T_EProdL : forall e t1 t2,
  has_type Phi Delta Gamma e (prod t1 t2) ->
  has_type Phi Delta Gamma (left_tm e) t1
| T_EProdR : forall e t1 t2,
  has_type Phi Delta Gamma e (prod t1 t2) ->
  has_type Phi Delta Gamma (right_tm e) t2
| T_ISumL : forall e t1 t2,
  has_type Phi Delta Gamma e t1 ->
  has_type Phi Delta Gamma (inl e) (sum t1 t2)
| T_ISumR : forall e t1 t2,
  has_type Phi Delta Gamma e t2 ->
  has_type Phi Delta Gamma (inr e) (sum t1 t2)
| T_ESum : forall e t1 t2 t e1 e2,
  has_type Phi Delta Gamma e (sum t1 t2) ->
  has_type Phi Delta (scons t1 Gamma) e1 t ->
  has_type Phi Delta (scons t2 Gamma) e2 t ->
  has_type Phi Delta Gamma (case e e1 e2) t
| T_IUniv : forall t0 t e,
  has_type Phi (lift_delta (scons t0 Delta)) (lift_gamma Gamma) e t ->
  has_type Phi Delta Gamma (tlam e) (all t0 t)
| T_EUniv : forall t t' t0 e,
 subtype Phi Delta t' t0 ->
 has_type Phi Delta Gamma e (all t0 t) ->
 has_type Phi Delta Gamma (tapp e) (subst_ty var_label (scons t' var_ty) t)
| T_IExist : forall e t t' t0,
  has_type Phi Delta Gamma e (subst_ty var_label (scons t' var_ty) t) ->
  subtype Phi Delta t' t0 ->
  has_type Phi Delta Gamma (pack e) (ex t0 t)
| T_EExist : forall e e' t0 t t',
  has_type Phi Delta Gamma e (all t0 t) ->
  has_type Phi (lift_delta (scons t0 Delta)) (scons t (lift_gamma Gamma)) e' (ren_ty id shift t') ->
  has_type Phi Delta Gamma (unpack e e') t'
| T_ILUniv : forall cs lab e t,
  has_type ((condition cs (var_label var_zero) (ren_label shift lab)) :: (lift_phi Phi)) 
                                        (lift_delta_l Delta) (lift_gamma_l Gamma) e t ->
  has_type Phi Delta Gamma (l_lam e) (all_l cs lab t)
| T_ELUniv : forall cs lab lab' e t,
  (Phi |= (condition cs lab lab')) ->
  has_type Phi Delta Gamma e (all_l cs lab t) ->
  has_type Phi Delta Gamma (lapp e lab') (subst_ty (scons lab' var_label) var_ty t)
| T_Lem : forall co e t,
  has_type (co :: Phi) Delta Gamma e t ->
  has_type ((negate_cond co) :: Phi) Delta Gamma e t ->
  has_type Phi Delta Gamma e t
| T_LIf : forall co e1 e2 t,
  has_type (co :: Phi) Delta Gamma e1 t ->
  has_type (co :: Phi) Delta Gamma e2 t ->
  has_type Phi Delta Gamma (if_c co e1 e2) t
| T_Sync : forall e (pf : l > 0),
  has_type Phi Delta Gamma e (Data (adv pf)) ->
  has_type Phi Delta Gamma (sync e) (Data (adv pf))
| T_Sub : forall e t t',
  subtype Phi Delta t t' ->
  has_type Phi Delta Gamma e t ->
  has_type Phi Delta Gamma e t'.