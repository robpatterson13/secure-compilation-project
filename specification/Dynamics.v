Require Import String List.
Import ListNotations.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_val : nat -> tm
| tm_bin : tm -> tm -> tm
| tm_un : tm -> tm
| tm_let : string -> tm -> tm -> tm.


Fixpoint subst (x : string) (s : nat) (t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb x y then tm_val s else t
  | tm_val _ => t 
  | tm_bin t1 t2 => tm_bin (subst x s t1) (subst x s t2)
  | tm_un t1 => tm_un (subst x s t1)
  | tm_let x_b e b =>
      let body := if String.eqb x x_b then b else (subst x s b) in
      tm_let x_b (subst x s e) body
  end.

Definition smap : Type := list (string * nat).

Fixpoint subst_many (bindings : smap) (t : tm) : tm :=
  match bindings with
  | [] => t
  | (x, e) :: rest =>
      let t' := subst x e t in
      subst_many rest t'
  end.

Definition update {A} (Gamma : list (string * A)) (x : string) (t : A) : list (string * A) :=
  (x, t) :: Gamma.


Fixpoint lookup {A} (m : list (string * A)) (x : string) : option A :=
  match m with
  | [] => None
  | (y, t) :: m' =>
      if String.eqb x y then Some t
      else lookup m' x
  end.


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
  big_eval (subst x v1 e2) v2 -> 
  big_eval (tm_let x e1 e2) v2.

  Theorem big_eval_det (t : tm) (v1 v2 : nat) : 
  big_eval t v1 ->
  big_eval t v2 ->
  v1 = v2.
  intros h1; revert v2.
  induction h1.
  {
    intros v2 h2.
    inversion h2.
    reflexivity.
  }
  {
    intros v2 h2.
    subst.
    inversion h2; subst.
    rewrite (IHh1 _ H0).
    reflexivity.
  }
  {
    intros v3 h3.
    subst.
    inversion h3; subst.
    rewrite (IHh1_2 _ H2).
    rewrite (IHh1_1 _ H1).
    reflexivity.
  }
  {
    intros v0 h.
    inversion h; subst; clear h.
    specialize (IHh1_1 _ H3); subst.
    apply IHh1_2.
    apply H4.
  }
Qed.