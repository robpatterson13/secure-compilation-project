From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_val : nat -> tm
| tm_bin : tm -> tm -> tm
| tm_un : tm -> tm
| tm_let : string -> tm -> tm -> tm.

Inductive ty : Type :=
| Pub : ty
| Sec : ty.
    
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb x y then s else t
  | tm_val _ => t 
  | tm_bin t1 t2 => tm_bin (subst x s t1) (subst x s t2)
  | tm_un t1 => tm_un (subst x s t1)
  | tm_let x_b e b =>
      let body := if String.eqb x_b x then b else (subst x s b) in
      tm_let x_b (subst x s e) body
  end.

Definition smap : Type := list (string * tm).

Fixpoint subst_many (bindings : smap) (t : tm) : tm :=
  match bindings with
  | [] => t
  | (x, e) :: rest =>
      let t' := subst x e t in
      subst_many rest t'
  end.

Definition max (t1 : ty) (t2 : ty) :=
  match t1, t2 with
  | Pub, Pub => Pub
  | Pub, Sec => Sec
  | Sec, Pub => Sec
  | Sec, Sec => Sec
  end.

Definition context : Type := list (string * ty).

Definition update (Gamma : context) (x : string) (t : ty) : context :=
  (x, t) :: Gamma.

Fixpoint lookup (Gamma : context) (x : string) : option ty :=
  match Gamma with
  | [] => None
  | (y, t) :: Gamma' =>
      if String.eqb x y then Some t
      else lookup Gamma' x
  end.

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x t1,
    lookup Gamma x = Some t1 ->
    has_type Gamma (tm_var x) t1
| T_Val : forall Gamma v,
    has_type Gamma (tm_val v) Pub
| T_Un : forall Gamma e t,
    has_type Gamma e t ->
    has_type Gamma (tm_un e) t
| T_Bin : forall Gamma e1 e2 t1 t2,
    has_type Gamma e1 t1 ->
    has_type Gamma e2 t2 ->
    has_type Gamma (tm_bin e1 e2) (max t1 t2)
| T_Let : forall Gamma e1 e2 x t1 t2,
    has_type Gamma e1 t1 ->
    has_type (update Gamma x t1) e2 t2 ->
    has_type Gamma (tm_let x e1 e2) t2.
    
Axiom f_un : nat -> nat.
Axiom f_bin : nat -> nat -> nat.

Inductive big_eval : tm -> nat -> Prop := 
| Etm_val : forall v,
  big_eval (tm_val v) v
| Etm_un : forall e v v',
  big_eval e v -> v' = f_un v -> 
  big_eval (tm_un e) v'
| Etm_bin : forall e1 e2 v1 v2 v,
  big_eval e1 v1 -> 
  big_eval e2 v2 -> 
  v = f_bin v1 v2 -> 
  big_eval (tm_bin e1 e2) v
| Etm_let : forall x e1 e2 v1 v2,
  big_eval e1 v1 -> 
  big_eval (subst x (tm_val v1) e2) v2 -> 
  big_eval (tm_let x e1 e2) v2.

Inductive type_rel : ty -> nat -> nat -> Prop :=
| TR_Pub : forall v,
  type_rel Pub v v
| TR_Sec : forall v1 v2,
  type_rel Sec v1 v2.