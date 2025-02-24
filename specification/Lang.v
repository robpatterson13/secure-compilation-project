Require Import String List.
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

  
  
