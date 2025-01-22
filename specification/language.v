From Coq Require Import Strings.String.

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

Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).

Fixpoint subst_many (bindings : smap) (t : tm) : tm :=
  match bindings with
  | nil => t
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

