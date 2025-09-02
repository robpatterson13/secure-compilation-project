Require Import core fintype owl constants Dist.

Require Import List. 
Import ListNotations.
Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.
From Coq Require Import Arith.Arith.

(* Some nice Ltac *)
Ltac inv H := inversion H; subst.

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

(* Check if a constraint is valid, under the assumption it is closed - Boolean version *)
Definition valid_constraint_b (co : constr 0) : bool :=
  match co with
  | (condition Core.leq x y) => L.(leq) (interp_lattice x) (interp_lattice y) 
  | (condition geq x y) => L.(leq) (interp_lattice y) (interp_lattice x)
  | (condition gt x y) => L.(leq) (interp_lattice y) (interp_lattice x) && negb (L.(leq) (interp_lattice x) (interp_lattice y))
  | (condition lt x y) => L.(leq) (interp_lattice x) (interp_lattice y) && negb (L.(leq) (interp_lattice y) (interp_lattice x))
  | (condition nleq x y) => negb (L.(leq) (interp_lattice y) (interp_lattice x))
  | (condition ngeq x y) => negb (L.(leq) (interp_lattice y) (interp_lattice x))
  | (condition ngt x y) => negb (L.(leq) (interp_lattice y) (interp_lattice x)) || L.(leq) (interp_lattice x) (interp_lattice y)
  | (condition nlt x y) => negb (L.(leq) (interp_lattice x) (interp_lattice y)) || negb (L.(leq) (interp_lattice y) (interp_lattice x))
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

(* Checks for proper values within terms - Boolean version *)
Fixpoint is_value_b {l m} (t : tm l m) : bool :=
  match t with
  | error            => true
  | skip             => true
  | loc _            => true
  | bitstring _      => true
  | fixlam _         => true
  | tlam _           => true
  | l_lam _          => true
  | tm_pair v1 v2    => is_value_b v1 && is_value_b v2
  | inl v            => is_value_b v
  | inr v            => is_value_b v
  | pack v           => is_value_b v
  | _ => false
  end.

Definition is_value_or_var_b {l m} (t : tm l m) : bool :=
  match t with
  | var_tm _  => true
  | _ => (is_value_b t)
  end.

Inductive is_redex { l m } : tm l m -> Prop :=
| zero_redex : forall v,
  is_value v ->
  is_redex (zero v).

(* K context (continuance) for evaluation rules *)
Inductive Kctx {l m : nat} :=
| KHole : Kctx
| ZeroK : Kctx -> Kctx
| KAppL : Kctx -> tm l m -> Kctx
| KAppR : tm l m -> Kctx -> Kctx
| KAlloc : Kctx -> Kctx
| KDeAlloc : Kctx -> Kctx
| KAssignL : Kctx -> tm l m -> Kctx
| KAssignR : tm l m -> Kctx -> Kctx
| KPairL : Kctx -> tm l m -> Kctx
| KPairR : tm l m  -> Kctx -> Kctx
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
| KSync : Kctx -> Kctx
| KOpL : op ->  Kctx -> tm l m -> Kctx
| KOpR : op -> tm l m -> Kctx -> Kctx.

(* Plug a term into the expression context K to get a resulting term *)
Fixpoint Plug { l m } (K : Kctx) (t : tm l m) : (tm l m) :=
   match K with
   | KHole => t 
   | ZeroK K' => zero (Plug K' t)
   | KAppL K' e => (Core.app (Plug K' t) e)
   | KAppR  v K' => (Core.app v (Plug K' t))
   | KAlloc K' => (alloc (Plug K' t))
   | KDeAlloc K' => (dealloc (Plug K' t))
   | KAssignL K' e => (assign (Plug K' t) e)
   | KAssignR v K' => (assign v (Plug K' t))
   | KPairL K' e => (tm_pair (Plug K' t) e)
   | KPairR  v K' => (tm_pair v (Plug K' t))
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
   | KOpL f K' e => Op f (Plug K' t) e
   | KOpR f v K' => Op f v (Plug K' t)
   end.

(* Peace of mind for later on *)
Inductive wfKctx {l m} : (@Kctx l m) -> Prop :=
| wfKHole : wfKctx KHole
| wfZero : forall K, wfKctx K -> wfKctx (ZeroK K)
| wfAppL : forall K e, wfKctx K -> wfKctx (KAppL K e)
| wfAppR : forall v K, wfKctx K -> is_value_b v = true -> wfKctx (KAppR v K)
| wfAlloc : forall K, wfKctx K -> wfKctx (KAlloc K)
| wfDeAlloc : forall K, wfKctx K -> wfKctx (KDeAlloc K)
| wfAssignL : forall K e, wfKctx K -> wfKctx (KAssignL K e)
| wfAssignR : forall v K, wfKctx K -> is_value_b v = true -> wfKctx (KAssignR v K)
| wfPairL : forall K e, wfKctx K -> wfKctx (KPairL K e)
| wfPairR : forall v K, wfKctx K -> is_value_b v = true -> wfKctx (KPairR v K)
| wfFst : forall K, wfKctx K -> wfKctx (KFst K)
| wfSnd : forall K, wfKctx K -> wfKctx (KSnd K)
| wfInl : forall K, wfKctx K -> wfKctx (KInl K)
| wfInR : forall K, wfKctx K -> wfKctx (KInR K)
| wfCase : forall K e1 e2, wfKctx K -> wfKctx (KCase K e1 e2)
| wfTapp : forall K, wfKctx K -> wfKctx (KTapp K)
| wfLapp : forall K lab, wfKctx K -> wfKctx (KLapp K lab)
| wfPack : forall K, wfKctx K -> wfKctx (KPack K)
| wfUnpack : forall K e, wfKctx K -> wfKctx (KUnpack K e)
| wfIf : forall K e1 e2, wfKctx K -> wfKctx (KIf K e1 e2)
| wfSync : forall K, wfKctx K -> wfKctx (KSync K)
| wfOpL : forall f K e, wfKctx K -> wfKctx (KOpL f K e)
| wfOpR : forall f K v, wfKctx K -> is_value_b v = true -> wfKctx (KOpR f v K).

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

Fixpoint all_zero_b (b : binary) : bool :=
  match b with
  | (bone b') => false
  | (bzero b') => (all_zero_b b')
  | bend => true 
  end.

Definition mem (l m : nat) := nat -> option (tm l m).

(* Memory only contains value terms *)
Definition only_values {l m} (memory : mem l m) : Prop :=
  forall a t, memory a = Some t -> is_value_b t = true.

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

(* Encode this adversary... *)
Record Adv := {
  Arounds : binary -> nat;
  Ainit {l m} : binary -> Dist (@Kctx l m * (mem l m) * binary);
  Async : (binary * binary) -> Dist (binary * binary);
  Adecide : binary -> Dist binary;
}.


Definition fake_adv : Adv :=
  {|
    Arounds := (fun x => 999);
    Ainit := (fun l m x => Ret (KHole, test_mem l m, x));
    Async := (fun '(x, y) => Ret (x, y));
    Adecide := (fun x => Ret (x))
  |}.

Definition convert_to_bitstring (l d : nat) (bs : binary) : tm l d :=
   (bitstring bs).

Axiom fresh_not_allocated :
  forall {l m} (memory : mem l m), memory (fresh memory) = None.

(* General logic for non error reductions, and how they function *)

(* NEW STUFF TO WORK THROUGH *)

Definition extract_argument (e1 : tm 0 0) : option binary :=
  match e1 with
  | bitstring b => Some b
  | _ => None
  end.

Definition reduce (a : Adv) (t : tm 0 0) (memory : mem 0 0) (s : binary) : option (Dist (tm 0 0 * mem 0 0 * binary)) :=
  match t with 
  | zero (bitstring b) => Some (Ret ((bitstring (generate_zero b)), memory, s))
  | if_tm (bitstring b) e1 e2 => if all_zero_b b then Some (Ret (e1, memory, s)) else Some (Ret (e2, memory, s))
  | alloc v => if is_value_b v then (let res := (fresh memory) in Some (Ret (loc res, (allocate res v memory), s))) else None
  | dealloc (loc n) => 
    match memory n with
    | None => None
    | Some v => Some (Ret (v, memory, s))
    end
  | assign (loc n) v => if is_value_b v then Some (Ret (skip, (allocate n v memory), s)) else None
  | Core.app (fixlam e) v => if is_value_b v then Some (Ret ((subst_tm var_label (scons v (scons (fixlam e) var_tm)) e), memory, s)) else None
  | left_tm (tm_pair v1 v2) => if andb (is_value_b v1) (is_value_b v2) then Some (Ret (v1, memory, s)) else None
  | right_tm (tm_pair v1 v2) => if andb (is_value_b v1) (is_value_b v2) then Some (Ret (v2, memory, s)) else None
  | case (inl v) e1 e2 => if is_value_b v then Some (Ret (subst_tm var_label(scons v var_tm) e1, memory, s)) else None
  | case (inr v) e1 e2 => if is_value_b v then Some (Ret (subst_tm var_label (scons v var_tm) e2, memory, s)) else None
  | tapp (tlam e) => Some (Ret (e, memory, s))
  | lapp (l_lam e) lab => Some (Ret ((subst_tm (scons lab var_label) var_tm e), memory, s))
  | unpack (pack v) e => if is_value_b v then Some (Ret (subst_tm var_label (scons v var_tm) e, memory, s)) else None
  | if_c c e1 e2 => if valid_constraint_b c then Some (Ret (e1, memory, s)) else Some (Ret (e2, memory, s))
  | Op f e1 e2 => 
    match extract_argument e1 with 
    | None => None
    | Some b1 => 
      match extract_argument e2 with
      | None => None
      | Some b2 => Some (x <- (f b1 b2) ;; Ret (bitstring x, memory, s)) end end
  | sync (bitstring b) => Some (x <- (a.(Async) (b, s));; Ret (bitstring (fst x), memory, s))
  | _ => None
  end.

Lemma test_reduce : forall (memory : mem 0 0) s, 
  reduce fake_adv (zero (bitstring (bone (bone bend)))) memory s = Some (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  simpl. reflexivity.
Qed.

(* Unused... for now *)
Definition is_value_dec {l m} (t : tm l m) : { is_value_b t = true } + { not (is_value_b t = true) }.
Proof.
  destruct (is_value_b t) eqn:Hb.
  - left. reflexivity.
  - right. simpl. discriminate.
Qed.

Require Import Coq.Program.Equality.

Fixpoint decompose (e : tm 0 0) : option (Kctx * tm 0 0) :=
  match e with
  | zero e =>
      match decompose e with
      | None => Some (KHole, zero e) 
      | Some (K, r) => Some (ZeroK K, r)
      end
  | Core.app e1 e2 => 
    match decompose e1, decompose e2 with 
    | Some (K, r), _ => Some (KAppL K e2, r)
    | None, Some (K, r) => Some (KAppR e1 K, r)
    | _, _ => Some (KHole, Core.app e1 e2)
    end
  | alloc v => 
      match decompose v with
      | None => Some (KHole, alloc v) 
      | Some (K, r) => Some (KAlloc K, r)
      end
  | dealloc v =>
      match decompose v with
      | None => Some (KHole, dealloc v) 
      | Some (K, r) => Some (KDeAlloc K, r)
      end
  | assign e1 e2 =>
      match decompose e1, decompose e2 with
      | Some (K, r), _ => Some (KAssignL K e2, r)
      | None, Some (K, r) => Some (KAssignR e1 K, r)
      | _, _ => Some (KHole, assign e1 e2)
      end
  | tm_pair e1 e2 => 
      match decompose e1, decompose e2 with
      | Some (K, r), _ => Some (KPairL K e2, r)
      | None, Some (K, r) => Some (KPairR e1 K, r)
      | _, _ => None
      end
  | left_tm e =>
      match decompose e with 
      | Some (K, r) => Some (KFst K, r)
      | None => Some (KHole, left_tm e)
      end
  | right_tm e => 
      match decompose e with 
      | Some (K, r) => Some (KSnd K, r)
      | None => Some (KHole, right_tm e)
      end
  | inl e => 
      match decompose e with
      | Some (K, r) => Some (KInl K, r)
      | None => None
      end
  | inr e => 
      match decompose e with
      | Some (K, r) => Some (KInR K, r)
      | None => None
      end
  | case e0 e1 e2 =>
      match decompose e0 with
      | None => Some (KHole, case e0 e1 e2)
      | Some (K, r) => Some (KCase K e1 e2, r)
      end
  | tapp e =>
      match decompose e with
      | None => Some (KHole, tapp e)
      | Some (K, r) => Some (KTapp K, r)
      end
  | lapp e lab => 
      match decompose e with
      | None => Some (KHole, lapp e lab)
      | Some (K, r) => Some (KLapp K lab, r)
      end
  | pack e => 
      match decompose e with
      | None => None
      | Some (K, r) => Some (KPack K, r)
      end
  | unpack e1 e2 =>
      match decompose e1 with
      | None => Some (KHole, unpack e1 e2)
      | Some (K, r) => Some (KUnpack K e2, r)
      end   
  | if_tm v e1 e2 => 
      match decompose v with
      | None => Some (KHole, if_tm v e1 e2)
      | Some (K, r) => Some (KIf K e1 e2, r)
      end
  | if_c c e1 e2 => Some (KHole, if_c c e1 e2)
  | sync e =>
      match decompose e with 
      | None => Some (KHole, sync e)
      | Some (K, r) => Some (KSync K, r)
      end
  | Op f e1 e2 =>
    match decompose e1, decompose e2 with 
    | Some (K, r), _ => Some (KOpL f K e2, r)
    | None, Some (K, r) => Some (KOpR f e1 K, r)
    | _, _ => Some (KHole, Op f e1 e2)
    end
  | _ => None
  end.
  
(* Decompose Lemma 1 *)
Lemma unique_decomposition : forall (e : tm 0 0),
  (is_value_b e = true /\ decompose e = None) \/
    (is_value_b e = false /\
       exists (K : @Kctx 0 0) (r : tm 0 0),
         decompose e = Some (K, r)).
Proof.
  intros.
  dependent induction e; try (simpl; left; split; reflexivity; reflexivity).
  - destruct f.
  - simpl. right. split. reflexivity. destruct (decompose e1) eqn:He1; destruct (decompose e2) eqn:He2.
    + destruct p. exists (KOpL o k e2), t. reflexivity.
    + destruct p. exists (KOpL o k e2), t. reflexivity.
    + destruct p. exists (KOpR o e1 k), t. reflexivity.
    + exists (KHole), (Op o e1 e2). reflexivity.  
  - simpl. right. split. reflexivity. destruct (decompose e).
    + destruct p. exists (ZeroK k). exists t. reflexivity.
    + exists KHole. exists (zero e). simpl. reflexivity.
  - simpl. right. split. reflexivity. destruct (decompose e1) eqn:He1; destruct (decompose e2) eqn:He2.
    + destruct p. exists (KAppL k e2). exists t. reflexivity.
    + destruct p. exists (KAppL k e2). exists t. reflexivity.
    + destruct p. exists (KAppR e1 k), t. reflexivity. 
    + exists KHole. exists (Core.app e1 e2). reflexivity.
  - simpl. right. split. reflexivity. destruct (decompose e).
    + destruct p. exists (KAlloc k). exists t. reflexivity.
    + exists KHole. exists (alloc e). reflexivity.
  - simpl. right. split. reflexivity. destruct (decompose e).
    + destruct p. exists (KDeAlloc k), t. reflexivity.
    + exists KHole, (! e). reflexivity.
  - simpl. right. split. reflexivity. destruct (decompose e1) eqn:He1; destruct (decompose e2) eqn:He2.
    + destruct p. exists (KAssignL k e2), t. reflexivity.
    + destruct p. exists (KAssignL k e2), t. reflexivity.
    + destruct p. specialize (IHe1 e1 eq_refl eq_refl). destruct IHe1. reflexivity.
      * destruct H. exists (KAssignR e1 k), t. reflexivity.
      * destruct H. exists (KAssignR e1 k), t. reflexivity.
    + exists KHole, (assign e1 e2). reflexivity.
  - simpl.
    assert (e1 ~= e1 /\ e2 ~= e2 ) as Ho. {
      split; reflexivity; reflexivity.
    }
    destruct Ho. 
    specialize (IHe1 e1 eq_refl eq_refl H). specialize (IHe2 e2 eq_refl eq_refl H0).
    destruct IHe1; destruct IHe2.
    + destruct H1; destruct H2. repeat rewrite H1. repeat rewrite H2. simpl. left. split. reflexivity. 
      destruct (decompose e1); destruct (decompose e2); try inv H4.
      * destruct p. inv H3.
      * reflexivity.
    + destruct H1; destruct H2. repeat rewrite H1. repeat rewrite H2. simpl. right. split. reflexivity.
      destruct (decompose e1); destruct (decompose e2).
      * destruct p. exists (KPairL k e2), t. reflexivity.
      * destruct p. exists (KPairL k e2), t. reflexivity.
      * destruct p. exists (KPairR e1 k), t. reflexivity.
      * assumption.
    + destruct H1; destruct H2. repeat rewrite H1. repeat rewrite H2. simpl. right. split. reflexivity.
      destruct (decompose e1); destruct (decompose e2); try inv H4.
      * destruct p. exists (KPairL k e2), t. reflexivity.
      * assumption.
    + destruct H1; destruct H2. repeat rewrite H1. repeat rewrite H2. simpl. right. split. reflexivity.
      destruct (decompose e1); destruct (decompose e2).
      * destruct p. exists (KPairL k e2), t. reflexivity.
      * destruct p. exists (KPairL k e2), t. reflexivity.
      * destruct p. exists (KPairR e1 k), t. reflexivity.
      * assumption.
  - simpl. right. split. reflexivity.
    destruct (decompose e).
    + destruct p. exists (KFst k), t. reflexivity.
    + exists KHole, (left_tm e). auto.
  - simpl. right. split. reflexivity.
    destruct (decompose e).
    + destruct p. exists (KSnd k), t. reflexivity.
    + exists KHole, (right_tm e). auto.
  - simpl. specialize (IHe e eq_refl eq_refl).  
    assert (e ~= e) as E. reflexivity.
    specialize (IHe E). destruct IHe.
    + destruct H. rewrite H. left. split. reflexivity.
      destruct (decompose e).
      * destruct p. inversion H0.
      * reflexivity.
    + destruct H. rewrite H. right. split. reflexivity.
      destruct (decompose e).
      * destruct p. exists (KInl k), t. reflexivity.
      * destruct H0. destruct H0. inversion H0. 
  (* Tedious, finish later *)
 Admitted.

Fixpoint exec (a : Adv) (k : nat) (e : tm 0 0) (m : mem 0 0) (st : binary) : option (Dist (tm 0 0 * mem 0 0 * binary)) :=
  match k with 
  | 0 => if is_value_b e then Some (Ret (e, m, st)) else None
  | S k' => 
    if is_value_b e then Some (Ret (e, m, st))
    else 
    match decompose e with 
    | None => None
    | Some (K, r) => 
        uniform_bind (reduce a r m st) (fun '(e', m', s') => 
            exec a k' (Plug K e') m' s') end end.

(* Decompose Lemma 2 *)
Lemma eq_decompose : forall e K r,
  decompose e = Some (K, r) ->
  e = (Plug K r).
Proof.
  intros.
  dependent induction e; try inv H.
  - admit.
  - destruct (decompose e) eqn:He in H1. destruct p.
    + inversion H1; subst. specialize (IHe e eq_refl eq_refl).
      assert (e ~= e) as E. reflexivity.
      specialize (IHe E k r He). rewrite IHe. simpl. reflexivity.
    + inversion H1; subst. simpl. reflexivity.
  - destruct (decompose e1) eqn:He1; destruct (decompose e2) eqn:He2.
    + destruct p. inversion H1; subst.      
Admitted.

(* Decompose Lemma 3 *)
Lemma wf_decompose : forall (e : tm 0 0) K r,
  decompose e = Some (K, r) ->
  wfKctx K.
Proof.
  dependent induction e; intros K r H; simpl in H;
  try (inv H; constructor; fail).
  - simpl in H. admit.
  - destruct (decompose e) eqn:Hd.
    + destruct p. inv H. constructor. 
      assert (e ~= e) as E. reflexivity.
      specialize (IHe e eq_refl eq_refl E k r). apply IHe. apply Hd.
    + inv H. constructor.
Admitted.  

Lemma exec_monotonicity : forall a k k' e memory s D,
  exec a k e memory s = Some D ->
  k' >= k ->
  exec a k' e memory s = exec a k e memory s.
Proof.
  intros.
  revert e memory s D k' H0 H.
  induction k.
  - intros. inv H. destruct (is_value_b e) eqn:Hv.
    + rewrite <- H2 in H. unfold exec. inversion H0; subst.
      * reflexivity.
      * rewrite Hv. reflexivity.
    + inversion H2.
  - intros. specialize unique_decomposition as Hud.
    specialize (Hud e). destruct Hud.
    + destruct H1. unfold exec. destruct k'.
      * rewrite H1. inv H. rewrite H1 in H4. reflexivity.
      * rewrite H1. inv H. reflexivity.
    + destruct H1. destruct H2. destruct H2. specialize (eq_decompose e x x0 H2) as Hd. specialize H as H'.
      rewrite Hd in H. unfold exec in H. destruct (is_value_b (Plug x x0)) eqn:Hv.
      * inv H. rewrite H1 in Hv. inversion Hv. (* disproved *)
      * induction k'. inversion H0. destruct (decompose (Plug x x0)) eqn:HP.
        assert (Hkn : decompose (Plug x x0) = Some (x, x0)). {
          rewrite Hd in H2. apply H2.
        }
        rewrite Hkn in HP. inversion HP; subst. 
        destruct (reduce a x0 memory s) eqn:Hre. fold exec in H.
        set (K1 :=
          fun x1 =>
            let '(p,s') := x1 in let '(e',m') := p in
            exec a k  (Plug x e') m' s').
        set (K2 :=
          fun x1 =>
            let '(p,s') := x1 in let '(e',m') := p in
            exec a k' (Plug x e') m' s').
        specialize (uniform_bind_ext_on (Some d) K2 K1) as Hun.
        assert ((forall x : tm 0 0 * mem 0 0 * binary, inSupport d x -> K2 x = K1 x)) as Hfar. {
          intros x1 Hin.
          destruct x1 as [[e' m'] s'].
          destruct (uniform_bind_all_some _ _ _ H _ Hin).
          assert (Hge : k' >= k) by lia.
          specialize (IHk (Plug x e') m' s' x1 k' Hge H3).
          exact IHk.
        }
        specialize (Hun Hfar). unfold K2 in Hun. unfold K1 in Hun. rewrite <- Hun in H.
        unfold exec. rewrite H1. rewrite H2. destruct (reduce a x0 memory s). fold exec.
        inversion Hre; subst. apply Hun. reflexivity.
        inversion H.
        inversion H. 
Qed.

Lemma value_of_plug { l m : nat} :
  forall K (e : tm l m), wfKctx K -> is_value_b (Plug K e) = true -> is_value_b e = true.
Proof.
  intros K e HK.
  revert e.
  induction HK; try intros e'' Hv; try simpl in Hv; try assumption; try inversion Hv.
  - rewrite Hv. specialize (IHHK e'').
    destruct (andb_prop _ _ H0) as [HvK HvE]. specialize (IHHK HvK). apply IHHK.
  - rewrite Hv. specialize (IHHK e'').
    destruct (andb_prop _ _ H1) as [HvK HvE]. specialize (IHHK HvE). apply IHHK.
  - specialize (IHHK e'' Hv). rewrite IHHK. rewrite Hv. reflexivity.
  - specialize (IHHK e'' Hv). rewrite IHHK. rewrite Hv. reflexivity.
  - specialize (IHHK e'' Hv). rewrite IHHK; rewrite Hv. reflexivity.
Qed.

Lemma wf_value_plug {l m}: forall K (e : tm l m),
  is_value_b (Plug K e) = true ->
  wfKctx K.
Proof.
  intros.
  revert e H.
  induction K; try discriminate; try constructor; try simpl in H; try specialize (IHK e H); try apply IHK.
  - destruct (andb_prop _ _ H) as [HvK HvE].
    specialize (IHK e HvK). apply IHK.
  - destruct (andb_prop _ _ H) as [HvK HvE].
    specialize (IHK e HvE). apply IHK.
  - destruct (andb_prop _ _ H) as [HvK HvE]. assumption.
Qed.

Fixpoint Kcomp {l m} (K K0 : @Kctx l m) : @Kctx l m :=
  match K with
  | KHole => K0
  | ZeroK K' => ZeroK (Kcomp K' K0)
  | KAppL K' e2 => KAppL (Kcomp K' K0) e2
  | KAppR v  K' => KAppR v (Kcomp K' K0)
  | KAlloc K' => KAlloc (Kcomp K' K0)
  | KDeAlloc K' => KDeAlloc(Kcomp K' K0)
  | KAssignL K' e2 => KAssignL (Kcomp K' K0) e2
  | KAssignR v  K' => KAssignR v (Kcomp K' K0)
  | KPairL K' e2 => KPairL (Kcomp K' K0) e2
  | KPairR v  K' => KPairR v (Kcomp K' K0)
  | KFst K' => KFst (Kcomp K' K0)
  | KSnd K' => KSnd (Kcomp K' K0)
  | KInl K' => KInl (Kcomp K' K0)
  | KInR K' => KInR (Kcomp K' K0)
  | KCase K' e1 e2 => KCase (Kcomp K' K0) e1 e2
  | KTapp K' => KTapp (Kcomp K' K0)
  | KLapp K' l => KLapp (Kcomp K' K0) l
  | KPack K' => KPack (Kcomp K' K0)
  | KUnpack K' e => KUnpack (Kcomp K' K0) e
  | KIf K' e1 e2 => KIf (Kcomp K' K0) e1 e2
  | KSync K' => KSync (Kcomp K' K0)
  | KOpL f K' e2 => KOpL f (Kcomp K' K0) e2
  | KOpR f v  K' => KOpR f v (Kcomp K' K0)
  end.

Lemma Plug_comp {l m} (K K0 : @Kctx l m) e :
  Plug (Kcomp K K0) e = Plug K (Plug K0 e).
Proof. 
  induction K; simpl; f_equal; auto.
Qed.

Lemma wfKctx_comp {l m} (K K0 : @Kctx l m) :
  wfKctx K -> wfKctx K0 -> wfKctx (Kcomp K K0).
Proof.
  intros.
  induction H; simpl; try constructor; eauto.
Qed.

Lemma decompose_plug K e K0 r :
  wfKctx K ->
  decompose e = Some (K0,r) ->
  decompose (Plug K e) = Some (Kcomp K K0, r).
Proof.
  intros.
  induction K; try simpl; try inv H; try specialize (IHK H2); try rewrite IHK; try reflexivity; try assumption.   
  - specialize (IHK H3). specialize (unique_decomposition t) as Hu. destruct Hu. destruct H1. rewrite H2. reflexivity.
    destruct H1. rewrite H1 in H4. discriminate H4.
  - specialize (IHK H3). specialize (unique_decomposition t) as Hu. destruct Hu. destruct H1. rewrite H2. reflexivity.
    destruct H1. rewrite H1 in H4. discriminate H4.
  - specialize (IHK H3). specialize (unique_decomposition t) as Hu. destruct Hu. destruct H1. rewrite H2. reflexivity.
    destruct H1. rewrite H1 in H4. discriminate H4.
  - specialize (IHK H3). specialize (unique_decomposition t) as Hu. destruct Hu. destruct H1. rewrite H2. reflexivity.
    destruct H1. rewrite H1 in H5. discriminate H5.
Qed.

Lemma uniform_bind_assoc {A B C}
      d (k1 : A -> option (Dist B)) (k2 : B -> option (Dist C)) :
  uniform_bind d (fun a => uniform_bind (k1 a) k2)
  = uniform_bind (uniform_bind d k1) k2.
Proof.
  revert k1 k2.
  induction d; intros k1 k2; simpl.
  induction a.
  - simpl. reflexivity.
  - specialize (H false) as Hf.
    specialize (H true) as Ht.
    simpl. rewrite Hf. rewrite Ht.
Admitted.

(* 5 Step plan *)
Lemma well_bracketed : forall a k K e memory s D,
  wfKctx K -> (* This is needed since K may not always be well formed *)
  exec a k (Plug K e) memory s = Some D ->
  (uniform_bind (exec a k e memory s) (fun '(e', m', s') =>(exec a k (Plug K e') m' s'))) = Some D.
Proof.
  induction k; intros K e memory s D H' H.
  (* k = 0 case *)
  specialize H as Hprime. 
  simpl in H.
  destruct (is_value_b (Plug K e)) eqn:Hp.
  assert (Some (ret (Plug K e, memory, s)) = 
          uniform_bind (Some (ret (e, memory, s))) (fun '(e', m', s') => (Some (ret (Plug K e', m', s'))))).
  simpl. reflexivity.
  assert (uniform_bind (Some (ret (e, memory, s))) (fun '(e', m', s') => (Some (ret (Plug K e', m', s')))) =
          uniform_bind (exec a 0 e memory s) (fun '(e', m', s') => (exec a 0 (Plug K e') m' s'))).
  simpl. specialize (value_of_plug K e) as Hpl.
  specialize (wf_value_plug K e Hp) as Hwfv.
  specialize (Hpl Hwfv Hp). rewrite Hpl. simpl. rewrite Hp. reflexivity.
  simpl in Hprime. rewrite Hp in Hprime. rewrite H0 in Hprime. rewrite H1 in Hprime. rewrite <- Hprime.
  simpl. inv H. reflexivity. inv H.
  (* k + 1 case goes/starts here *)
  (* e is a value *)
  destruct (unique_decomposition e). destruct H0.
  - assert (exec a (S k) (Plug K e) memory s  = 
            uniform_bind (Some (ret (e, memory, s))) (fun '(e', m', s') => (exec a (S k) (Plug K e') m' s'))).
    simpl. simpl in H. destruct (is_value_b (Plug K e)). reflexivity. reflexivity.
    assert (uniform_bind (Some (ret (e, memory, s)))
              (fun '(p, s') => let '(e', m') := p in exec a (S k) (Plug K e') m' s') =
            uniform_bind (exec a (S k) e memory s)
              (fun '(p, s') => let '(e', m') := p in exec a (S k) (Plug K e') m' s')).
    simpl. simpl in H. destruct (is_value_b (Plug K e)) eqn:Hj. rewrite H0. simpl. rewrite Hj. reflexivity. 
    destruct (decompose (Plug K e)) eqn:Hdes. simpl. destruct p. rewrite H0. simpl. rewrite Hj. rewrite Hdes. reflexivity. 
    inversion H.
    rewrite <- H. rewrite H2. rewrite H3. reflexivity.
  (*e is not a value *)
  - specialize (eq_decompose) as Hded.
    destruct H0. destruct H1 as [K0]. destruct H1 as [r].
    specialize (Hded e K0 r H1). rewrite Hded in H.
    (* step 1 *)
    assert (exec a (S k) (Plug K (Plug K0 r)) memory s =
            uniform_bind (reduce a r memory s) (fun '(e', m', s') => (exec a k (Plug K (Plug K0 e')) m' s'))).
    rewrite Hded in *.
    unfold exec at 1.
    destruct (is_value_b (Plug K (Plug K0 r))) eqn:Hy.
    specialize (wf_value_plug K (Plug K0 r) Hy). intros.
    specialize (value_of_plug K (Plug K0 r) H2 Hy). intros.
    rewrite H3 in H0. inversion H0.
    rewrite (decompose_plug K _ _ _ H' H1).
    f_equal.
    apply functional_extensionality. intros. 
    destruct x; simpl. fold exec. destruct p; simpl.
    rewrite Plug_comp. reflexivity.
    (* step 2 - Inductive - *)
    assert (uniform_bind (reduce a r memory s) (fun '(e', m', s') => (exec a k (Plug K (Plug K0 e')) m' s')) =
            uniform_bind (reduce a r memory s) (fun '(e', m', s') => 
                                                    (uniform_bind (exec a k (Plug K0 e') m' s') (fun '(e'', m'', s'') => (exec a k (Plug K e'') m'' s''))))).
    set (K2 :=
        fun '(p,s') => let '(e',m') := p in exec a k (Plug K (Plug K0 e')) m' s').
    set (K1 :=
        fun '(p,s') => let '(e',m') := p in
          uniform_bind (exec a k (Plug K0 e') m' s')
            (fun '(p0,s'') => let '(e'',m'') := p0 in exec a k (Plug K e'') m'' s'')).
    assert (uniform_bind (reduce a r memory s) K2 = Some D). unfold K2. rewrite <- H2. apply H.
    eapply uniform_bind_ext_on. intros [[e' m'] s'] Hin.
    destruct (uniform_bind_all_some _ _ _ H3 _ Hin) as [Dleaf HK2x].
    specialize (IHk K (Plug K0 e') m' s' Dleaf). 
    simpl in HK2x. 
    specialize (IHk H' HK2x). 
    rewrite <- IHk in HK2x. 
    apply HK2x. 
    (* step 3 *)    
    assert (uniform_bind (reduce a r memory s) 
                         (fun '(e', m', s') => 
                                (uniform_bind (exec a k (Plug K0 e') m' s') 
                                              (fun '(e'', m'', s'') => 
                                                     (exec a k (Plug K e'') m'' s'')))) =
            uniform_bind (exec a (S k) (Plug K0 r) memory s) 
                         (fun '(e', m', s') => (exec a k (Plug K e') m' s'))).
    simpl. rewrite Hded in H0. rewrite H0. rewrite Hded in H1. rewrite H1.
    set (K1 :=
      fun '(p,s') =>
        let '(e',m') := p in exec a k (Plug K0 e') m' s'). 
    set (K2 :=
      fun '(p0,s'') =>
        let '(e'',m'') := p0 in exec a k (Plug K e'') m'' s'').
    specialize (uniform_bind_assoc (reduce a r memory s) K1 K2) as Hassoc.
    rewrite <- Hassoc.
    assert ((fun '(p, s') => let '(e', m') := p in uniform_bind (exec a k (Plug K0 e') m' s') K2) =
            (fun a : tm 0 0 * mem 0 0 * binary => uniform_bind (K1 a) K2)).
    apply functional_extensionality.
    intros.
    destruct x. destruct p. unfold K1. reflexivity.
    rewrite H4. reflexivity.
    (* step 4 *)
    assert (uniform_bind (exec a (S k) (Plug K0 r) memory s) (fun '(e', m', s') => (exec a k (Plug K e') m' s')) =
            uniform_bind (exec a (S k) e memory s) (fun '(e', m', s') => (exec a k (Plug K e') m' s'))).
    rewrite Hded. reflexivity.
    (* step 5 *)
    assert (uniform_bind (exec a (S k) e memory s) (fun '(e', m', s') => (exec a k (Plug K e') m' s')) =
            uniform_bind (exec a (S k) e memory s) (fun '(e', m', s') => (exec a (S k) (Plug K e') m' s'))).
    specialize (uniform_bind_ext_on (exec a (S k) e memory s)
                  (fun '(e', m', s') => (exec a k (Plug K e') m' s')) 
                  (fun '(e', m', s') => (exec a (S k) (Plug K e') m' s'))) as Hi.
    apply Hi. intros.
    assert ((forall x : tm 0 0 * mem 0 0 * binary,
              inSupportUniform (exec a (S k) e memory s) x ->
              (fun '(p, s') => let '(e', m') := p in exec a k (Plug K e') m' s') x =
              (fun '(p, s') => let '(e', m') := p in exec a (S k) (Plug K e') m' s') x)).
    intros. 
    rewrite H2 in H.
    rewrite H3 in H.
    rewrite H4 in H.
    rewrite H5 in H.
    specialize (uniform_bind_all_some (exec a (S k) e memory s)
                  (fun '(p, s') => let '(e', m') := p in exec a k (Plug K e') m' s') D H x0 H7) as Hsus.
    destruct Hsus. destruct x0. destruct p.
    specialize (exec_monotonicity a k (S k) (Plug K t) m b x1 H8) as Hem.
    assert (S k >= k). lia. specialize (Hem H9). symmetry in Hem. apply Hem.
    specialize (H7 x H6). simpl in H7. simpl. apply H7.
    (* Wrap up the chain via rewrites *)
    rewrite <- H.
    rewrite H2.
    rewrite H3.
    rewrite H4.
    rewrite H5.
    rewrite H6.
    reflexivity.
Qed.

(** TODO:
  - Move uniform_bind into Dist.v DONE
  - Finish decompose, spec out Lemma 1 (Lemma 1 is correctness for decompose) SORT OF Done, just tedious
  - Encoding the adversary TBD, easy but I've got bigger fish to fry
  - Finish reduce; get rid of Inductive versions DONE
  - Do monotonicity lemma DONE
  - Well-bracketed lemma DONE 
  - Make Op binary DONE *)

Definition plug_dist (K : Kctx) (c : (tm 0 0 * mem 0 0 * binary)) : (tm 0 0 * mem 0 0 * binary) :=
  let '(e,m,s) := c in (Plug K e, m, s).

(* Sample Coin Flip Op *)
Definition coin_flip : op :=
  fun (x1 x2 : binary) =>
    b <- flip ;;
    ret (if b then bone bend else bzero bend).

(* Sample Coin Flip Op *)
Definition coin_flip_plus : op :=
  fun (x1 x2 : binary) =>
    b <- flip ;;
    ret (if b then x1 else x2).

Definition double_coin_flip : op :=
  fun (x1 x2 : binary) =>
    a <- flip ;;
    b <- flip ;;
    ret (if a then x1 else if b then x2 else bzero bend).

(* Quick unfold *)
Lemma tester :
  coin_flip = coin_flip.
Proof.
  unfold coin_flip. simpl. reflexivity.
Qed.

(* Quick unfold 2 *)
Lemma tester2 :
  double_coin_flip = double_coin_flip.
Proof.
  unfold double_coin_flip. simpl. reflexivity.
Qed.

Definition coin_Op : tm 0 0 := (Op coin_flip (bitstring bend) (bitstring bend)).

Definition coin_Op_plus : tm 0 0 := (Op coin_flip_plus (bitstring (bone (bone bend)))  (bitstring (bone bend))).

(* Test step/execute lemmas to see if we're in the correct place *)
Lemma coin_test : forall memory s,
  exec fake_adv 100 coin_Op memory s = Some (Flip (fun b => ret (bitstring (if b then bone bend else bzero bend), memory, s))).
Proof.
  intros.
  simpl.
  repeat (apply f_equal).
  apply functional_extensionality.
  intros.
  destruct x; reflexivity.
Qed.

Lemma exec_coin_Op_plus :
  forall (memory : mem 0 0) s,
    exec fake_adv 10 (zero coin_Op_plus) memory s = Some
             (Flip (fun b =>
                      ret (bitstring (if b then (bzero (bzero bend)) else bzero bend), memory, s))).
Proof.
  intros.
  simpl.
  apply f_equal.
  apply f_equal.
  apply functional_extensionality.
  destruct x; reflexivity.
Qed.

Lemma test_exec :
  forall (memory : mem 0 0) s,
    exec fake_adv 10 (zero (bitstring (bone (bone bend)))) memory s = Some (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  simpl. 
  reflexivity.
Qed.

Lemma test_exec_2 :
  forall (memory : mem 0 0) s,
    exec fake_adv 10 (zero (zero (bitstring (bone (bone bend))))) memory s = Some (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
  
Lemma test_error :
  forall (memory : mem 0 0) s,
    exec fake_adv 5 (zero skip) memory s = None.
Proof.
  intros.
  simpl.
  reflexivity.
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