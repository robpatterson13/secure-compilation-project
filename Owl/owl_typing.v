Require Import core fintype owl constants Dist.

Require Import List. 
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Setoid Morphisms Relation_Definitions.
From Coq Require Import Arith.Arith.

Record Adv := {
}.

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

Inductive is_redex { l m } : tm l m -> Prop :=
| zero_redex : forall v,
  is_value v ->
  is_redex (zero v).

(* K context (continuance) for evaluation rules *)
Inductive Kctx {l m : nat} :=
| KHole : Kctx
| ZeroK : Kctx -> Kctx
| KAppL : Kctx -> tm l m -> Kctx
| KAppR : forall (v : tm l m), is_value_b v = true -> Kctx -> Kctx
| KAlloc : Kctx -> Kctx
| KDeAlloc : Kctx -> Kctx
| KAssignL : Kctx -> tm l m -> Kctx
| KAssignR : forall (v : tm l m), is_value_b v = true -> Kctx -> Kctx
| KPairL : Kctx -> tm l m -> Kctx
| KPairR : forall (v : tm l m), is_value_b v = true -> Kctx -> Kctx
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
| KOp : forall (f : op) (vs : list (tm l m)) (K  : Kctx) (es : list (tm l m)),          
            Forall (fun v => is_value_b v = true) vs -> Kctx.

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
   | KOp f vs K' es _ => Op f (vs ++ Plug K' t :: es)
   end.

Fixpoint split_values {l m}
         (xs : list (tm l m))
  : list (tm l m) * list (tm l m) :=
  match xs with
  | [] => ([], [])
  | x :: xs' =>
      if is_value_b x
      then let (vs, es) := split_values xs' in (x :: vs, es)
      else ([], xs)
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

Definition convert_to_bitstring (l d : nat) (bs : binary) : tm l d :=
   (bitstring bs).

Axiom fresh_not_allocated :
  forall {l m} (memory : mem l m), memory (fresh memory) = None.

(* General logic for non error reductions, and how they function *)

(* NEW STUFF TO WORK THROUGH *)

Fixpoint extract_arguments (es : list (tm 0 0)) : option (list binary) :=
  match es with
  | [] => Some []
  | bitstring b :: es' =>
      match extract_arguments es' with
      | Some bs => Some (b :: bs)
      | None => None
      end
  | _ => None
  end.

Definition reduce (t : tm 0 0) (memory : mem 0 0) (s : binary) : option (Dist (tm 0 0 * mem 0 0 * binary)) :=
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
  | Op f es => 
    match extract_arguments es with 
    | None => None
    | Some bs => Some (x <- f bs ;; Ret (bitstring x, memory, s)) end
  | _ => None
  end.

Lemma test_reduce : forall (memory : mem 0 0) s, 
  reduce (zero (bitstring (bone (bone bend)))) memory s = Some (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  intros.
  simpl. reflexivity.
Qed.

Definition is_value_dec {l m} (t : tm l m) : { is_value_b t = true } + { not (is_value_b t = true) }.
Proof.
  destruct (is_value_b t) eqn:Hb.
  - left. reflexivity.
  - right. simpl. discriminate.
Qed.

Definition is_value_list {l m} (es : list (tm l m)) : Forall (fun v => is_value_b v = true) (fst (split_values es)).
  Proof.
    induction es.
    - simpl. constructor.
    - simpl. destruct (is_value_b a) eqn:Ha. 
      + simpl. destruct (split_values es). simpl. simpl in IHes. constructor. assumption. assumption.
      + simpl. constructor.
Qed.
      
Fixpoint decompose (e : tm 0 0) : option (@Kctx 0 0 * tm 0 0) :=
  match e with
  | zero e =>
      match decompose e with
      | None => Some (KHole, zero e) 
      | Some (K, r) => Some (ZeroK K, r)
      end
  | Core.app e1 e2 => 
    match decompose e1, decompose e2 with 
    | Some (K, r), _ => Some (KAppL K e2, r)
    | None, Some (K, r) => 
      match is_value_dec e1 with
      | left Hv => Some (KAppR e1 Hv K, r)
      | right _ => None (* Technically an impossible case, but oh well *)
      end
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
      | None, Some (K, r) => 
        match is_value_dec e1 with
        | left Hv => Some (KAssignR e1 Hv K, r)
        | right _ => None
        end
      | _, _ => Some (KHole, assign e1 e2)
      end
  | tm_pair e1 e2 => 
      match decompose e1, decompose e2 with
      | Some (K, r), _ => Some (KPairL K e2, r)
      | None, Some (K, r) => 
        match is_value_dec e1 with
        | left Hv => Some (KPairR e1 Hv K, r)
        | right _ => None
        end
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
  | Op f es => 
      match snd (split_values es) with 
      | [] => Some (KHole, Op f es)
      | e :: es' => 
          match decompose e with
          | Some (K, r) => Some (KOp f (fst (split_values es)) K es' (is_value_list es), r) 
          | None => None
          end
      end
  | _ => None
  end.

Fixpoint uniform_bind {A} {B} (c : Dist A) (k : A -> option (Dist B)) : option (Dist B) :=
  match c with 
  | Ret x => k x
  | Flip f => 
    match uniform_bind (f false) k, uniform_bind (f true) k with 
    | Some d1, Some d2 => Some (Flip (fun b => if b then d2 else d1))
    | _, _ => None end end.


Fixpoint exec (k : nat) (e : tm 0 0) (m : mem 0 0) (st : binary) : option (Dist (tm 0 0 * mem 0 0 * binary)) :=
  match k with 
  | 0 => if is_value_b e then Some (Ret (e, m, st)) else None
  | S k' => 
    if is_value_b e then Some (Ret (e, m, st))
    else 
    match decompose e with 
    | None => None
    | Some (K, r) => 
        match reduce r m st with 
        | None => None 
        | Some D => 
          uniform_bind D (fun '(e', m', s') => 
            exec k' (Plug K e') m' s') end end end.


(** TODO:
  - Move uniform_bind into Dist.v
  - Finish decompose, spec out Lemma 1 (Lemma 1 is correctness for decompose)
  - Encoding the adversary
  - Finish reduce; get rid of Inductive versions
  - Do monotonicity lemma
  - Well-bracketed lemma
  *)

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
  
(* General logic for evaluating a term down/performing steps of an execution *)
(* C represents some sort of Exec function *)
Inductive exec : nat -> (tm 0 0 * mem 0 0 * binary) -> Dist (tm 0 0 * mem 0 0 * binary) -> Prop :=
| exec_return : forall k e m s,
  is_value e \/ k = 0 ->
  exec k (e, m, s) (ret (e, m, s))
| exec_step :
    forall k K r m s D C,
      reduce (r, m, s) D ->
      (forall c, inSupport D c -> exec k (plug_dist K c) (C c)) ->
      exec (S k) (Plug K r, m, s) (c <- D ;; C c).

(* Potentially useful supporting lemma for Return dists *)
Lemma exec_step_ret : forall k K r m s c R,
  reduce (r, m, s) (Ret c) ->
  exec k (plug_dist K c) R ->
  exec (S k) (Plug K r, m, s) R.
Proof.
  intros.
  specialize (exec_step k K r m s (ret c) (fun x => R) H) as Hs.
  simpl in Hs. apply Hs.
  intros.
  unfold inSupport in H1. rewrite H1. assumption.  
Qed.

(* Potentially useful supporting lemma for Flip dists *)
Lemma exec_step_flip :
  forall k K r m s f C,
    reduce (r,m,s) (Flip f) ->
    (forall b c, inSupport (f b) c ->
                 exec k (plug_dist K c) (C c)) ->
    exec (S k) (Plug K r, m, s)
         (Flip (fun b => (c <- f b ;; C c))).
Proof.
  intros. 
  specialize (exec_step k K r m s (Flip f) C H) as He.
  apply He.
  intros. simpl in H1.
  destruct H1.
  - specialize (H0 false c H1) as Hw. apply Hw.
  - specialize (H0 true c H1) as Hw. apply Hw.
Qed.

(* Sample Coin Flip Op *)
Definition coin_flip : op :=
  fun (x : list binary) =>
    b <- flip ;;
    ret (if b then bone bend else bzero bend).

Definition first_binary (xs : list binary) : binary :=
  match xs with
  | x :: _ => x
  | []     => bend
  end.

Definition second_binary (xs : list binary) : binary :=
  match xs with
  | _ :: y :: _ => y
  | _           => bend
  end.

(* Sample Coin Flip Op *)
Definition coin_flip_plus : op :=
  fun (x : list binary) =>
    b <- flip ;;
    ret (if b then (first_binary x) else (second_binary x)).

Definition double_coin_flip : op :=
  fun (x : list binary) =>
    a <- flip ;;
    b <- flip ;;
    ret (if a then (first_binary x) else if b then (first_binary x) else bzero bend).

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

Definition coin_Op : tm 0 0 := (Op coin_flip []).

Definition coin_Op_plus : tm 0 0 := (Op coin_flip_plus [(bitstring (bone (bone bend))) ; (bitstring (bone bend))]).

Definition C_zero (c : tm 0 0 * mem 0 0 * binary) : Dist (tm 0 0 * mem 0 0 * binary) :=
  match c with
  | (bitstring b, m', s') => ret (bitstring (generate_zero b), m', s')
  | (e, m', s')  => ret (e, m', s') 
  end.

Lemma exec_coin_Op_plus :
  forall (memory : mem 0 0) s,
    exec 10 ((zero coin_Op_plus), memory, s)
             (Flip (fun b =>
                      ret (bitstring (if b then (bzero (bzero bend)) else bzero bend), memory, s))).
Proof.
  intros.
  assert ((Plug (ZeroK KHole) coin_Op_plus) = (zero coin_Op_plus)) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht. 
  specialize (exec_step 9 (ZeroK KHole) coin_Op_plus memory s) as Hf.
  specialize (Hf (Flip (fun b => ret (bitstring (if b then (bone (bone bend)) else bone bend), memory, s)))).
  simpl in Hf.
  specialize (Hf C_zero).
  simpl in Hf.
  assert ((fun x : bool =>
           ret (@bitstring 0 0 (generate_zero (if x then bone (bone bend) else bone bend)), memory, s)) = 
          (fun b : bool => 
           ret (bitstring (if b then bzero (bzero bend) else bzero bend), memory, s))) as Htr.
  {
    simpl.
    apply functional_extensionality. destruct x.
    - simpl. reflexivity.
    - simpl. reflexivity. 
  }
  rewrite Htr in Hf. 
  apply Hf.
  - specialize (r_op coin_flip_plus [(bitstring (bone (bone bend))) ; (bitstring (bone bend))] [(bone (bone bend)) ; (bone bend)]) as Hp.
    specialize (Hp memory s).
    assert ([bitstring (bone (bone bend)); bitstring (bone bend)] =
     list_map (convert_to_bitstring 0 0) [bone (bone bend); bone bend]) as Heq.
     {
      reflexivity.
     }
    specialize (Hp Heq). simpl in Hp.
    apply reduce_tm in Hp.
    unfold coin_Op_plus.
    apply Hp.
  - intros.
    clear Ht Hf Htr.
    destruct H.
    + rewrite H. simpl. 
Admitted.

Lemma exec_coin_Op :
  forall (memory : mem 0 0) s,
    exec 10 (Op coin_flip [], memory, s)
             (Flip (fun b =>
                      ret (bitstring (if b then bone bend else bzero bend), memory, s))).
Proof.
  intros.
  assert ((Plug KHole (Op coin_flip [])) = Op coin_flip []) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht.
  specialize (exec_step_flip 9 KHole (Op coin_flip []) memory s) as Hf.
  specialize (Hf (fun b => ret (bitstring (if b then bone bend else bzero bend), memory, s))).
  simpl in Hf.
  specialize (Hf (fun x => (ret x))).
  simpl in Hf.
  specialize (r_op coin_flip [] [] memory s) as Ho. simpl in Ho.
  assert (forall (lst : list (tm 0 0)), lst = lst) as free. {
    intros.
    reflexivity.
  }
  specialize (Ho (free [])).
  specialize (reduce_tm (Op coin_flip [], memory, s) (Flip (fun x : bool => ret (bitstring (if x then bone bend else bzero bend), memory, s)))) as Hr.
  specialize (Hr Ho).
  specialize (Hf Hr).
  specialize (Hf).
  apply Hf. intros.
  inversion H; subst. simpl.
  constructor. left. constructor.
Qed.

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
  specialize (exec_step_ret 9 KHole (zero (bitstring (bone (bone bend)))) memory s ((bitstring (bzero (bzero bend))), memory, s)) as Hn.
  simpl in Hn.
  specialize (Hn (ret ((bitstring (bzero (bzero bend))), memory, s))).
  simpl in Hn.
  specialize (r_zero (bone (bone bend)) memory s) as Hx. simpl in Hx.
  specialize (reduce_tm (zero (bitstring (bone (bone bend))), memory, s) (ret (bitstring (bzero (bzero bend)), memory, s)) Hx) as Hr.
  specialize (Hn Hr). simpl.
  apply Hn.
  constructor. 
  left.
  constructor.
Qed.

Lemma test_exec_2 :
  forall (memory : mem 0 0) s,
    exec 10 ((zero (zero (bitstring (bone (bone bend))))), memory, s) (ret ((bitstring (bzero (bzero bend))), memory, s)).
Proof.
  (* Exec Step 1 *)
  intros.
  assert ((Plug (ZeroK KHole) (zero (bitstring (bone (bone bend))))) = (zero (zero (bitstring (bone (bone bend)))))) as Ht. {
    simpl. reflexivity.
  }
  rewrite <- Ht. 
  specialize (exec_step_ret 9 (ZeroK KHole) (zero (bitstring (bone (bone bend)))) memory s ((bitstring (bzero (bzero bend))), memory, s) (ret ((bitstring (bzero (bzero bend))), memory, s))) as Hes.
  simpl in Hes.
  specialize (r_zero (bone (bone bend)) memory s) as Hx.
  specialize (reduce_tm (zero (bitstring (bone (bone bend))), memory, s) (ret(bitstring (bzero (bzero bend)), memory, s))) as Hr.
  specialize (Hr Hx).
  specialize (Hes Hr).
  simpl.
  apply Hes.
  (* Exec Step 2 *)
  simpl.
  clear Hr Hx Hes Ht. 
  assert ((Plug KHole (zero (bitstring (bzero (bzero bend))))) = (zero (bitstring (bzero (bzero bend))))) as Ht. {
    simpl. reflexivity.
  }
  specialize (exec_step_ret 8 KHole (zero (bitstring (bzero (bzero bend)))) memory s ((bitstring (bzero (bzero bend))), memory, s)) as Hs.
  specialize (Hs (ret ((bitstring (bzero (bzero bend))), memory, s))).
  specialize (r_zero (bzero (bzero bend)) memory s) as Hz.
  specialize (reduce_tm (zero (bitstring (bzero (bzero bend))), memory, s) (ret (bitstring (generate_zero (bzero (bzero bend))), memory, s)) Hz) as Hr.
  specialize (Hs Hr). 
  apply Hs.
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
  specialize (exec_step_ret 4 KHole (zero skip) memory s (error, memory, s)) as Hx.
  simpl in Hx.
  specialize (Hx (ret (error, memory, s))). simpl in Hx.
  specialize (Hx Hr).
  apply Hx.
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