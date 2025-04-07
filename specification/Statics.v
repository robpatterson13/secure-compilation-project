From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import Dynamics.

Inductive ty := 
  | Pub
  | Middle
  | Sec.

Scheme Equality for ty.

Record Lattice := {
    carrier : Set;
    le : carrier -> carrier -> bool;
    max : carrier -> carrier -> carrier;
    return_max: forall t1 t2, max t1 t2 = t1 \/ max t1 t2 = t2;
    order_max: forall t1 t2, max t1 t2 = max t2 t1;
    bot : carrier;
    bot_le : forall x, le bot x = true;
    refl_le : forall t, le t t = true;
    assym_le : forall t1 t2, le t1 t2 = true -> le t2 t1 = true -> t1 = t2;
    max_le: forall t1 t2 t3, le t1 t2 = false -> max t3 t1 = t3 -> le t3 t2 = false
}.

Section Types.
  Variable (L : Lattice).

Definition context : Type := list (string *  (L.(carrier))). 

Inductive has_type : context -> tm -> L.(carrier) -> Prop :=
| T_Var : forall Gamma x t1,
    lookup Gamma x = Some t1 ->
    has_type Gamma (tm_var x) t1
| T_Val : forall Gamma v,
    has_type Gamma (tm_val v) L.(bot)
| T_Un : forall Gamma e t,
    has_type Gamma e t ->
    has_type Gamma (tm_un e) t
| T_Bin : forall Gamma e1 e2 t1 t2,
    has_type Gamma e1 t1 ->
    has_type Gamma e2 t2 ->
    has_type Gamma (tm_bin e1 e2) (L.(max) t1 t2)
| T_Let : forall Gamma e1 e2 x t1 t2,
    has_type Gamma e1 t1 ->
    has_type (update Gamma x t1) e2 t2 ->
    has_type Gamma (tm_let x e1 e2) t2.


Definition base_max (t1 : ty) (t2 : ty) :=
  match t1, t2 with
  | Pub, Pub => Pub
  | Sec, Sec => Sec
  | Middle, Middle => Middle
  | Pub, Middle => Middle
  | Pub, Sec => Sec
  | Middle, Pub => Middle
  | Middle, Sec => Sec
  | Sec, Middle => Sec
  | Sec, Pub => Sec
  end.

Definition base_le (t1 t2 : ty) :=
match t1, t2 with
  | Pub, Pub => true
  | Sec, Sec => true
  | Middle, Middle => true
  | Pub, Middle => true
  | Pub, Sec => true
  | Middle, Sec => true
  | _ , _ => false
  end.

Lemma base_bot_le (t : ty):
  base_le Pub t = true.
Proof.
  destruct t; simpl; auto.
Qed.


Lemma base_le_reflexive (t: ty):
  base_le t t = true.
Proof.
  destruct t; simpl; reflexivity.
Qed.

Lemma base_le_assym (t1 t2 : ty):
  base_le t1 t2 = true -> base_le t2 t1 = true -> t1 = t2.
Proof.
intros h1 h2.
destruct t1; destruct t2; auto; discriminate.
Qed.

Lemma base_le_trans (t1 t2 t3: ty) :
  base_le t1 t2 = true -> base_le t2 t3 = true -> base_le t1 t3 = true.
Proof.
intros h1 h2.
destruct t1; destruct t2; destruct t3; auto.
Qed.

Lemma base_le_max_eq (t1 t2 : ty) : 
  base_le t1 t2 = true ->
  base_max t1 t2 = t2.
Proof.
intros h1.
destruct t1; destruct t2; simpl; auto; discriminate.
Qed.

End Types.
    