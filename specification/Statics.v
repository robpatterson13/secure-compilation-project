From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.
Require Import Dynamics.

Inductive ty :=
  | Pub
  | Middle
  | Sec.

Scheme Equality for ty.

Definition max (t1 : ty) (t2 : ty) :=
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

Definition le (t1 t2 : ty) :=
match t1, t2 with
  | Pub, Pub => true
  | Sec, Sec => true
  | Middle, Middle => true
  | Pub, Middle => true
  | Pub, Sec => true
  | Middle, Sec => true
  | _ , _ => false
  end.

Lemma le_reflexive (t: ty):
  le t t = true.
Proof.
  destruct t; simpl; reflexivity.
Qed.

Lemma le_assym (t1 t2 : ty):
  le t1 t2 = true -> le t2 t1 = true -> t1 = t2.
Proof.
intros h1 h2.
destruct t1; destruct t2; auto; discriminate.
Qed.

Lemma le_trans (t1 t2 t3: ty) :
  le t1 t2 = true -> le t2 t3 = true -> le t1 t3 = true.
Proof.
intros h1 h2.
destruct t1; destruct t2; destruct t3; auto.
Qed.

Lemma le_max_eq (t1 t2 : ty) : 
  le t1 t2 = true ->
  max t1 t2 = t2.
Proof.
intros h1.
destruct t1; destruct t2; simpl; auto; discriminate.
Qed.

Definition context : Type := list (string * ty).

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
    

(*
Idea: generalize type_rel to have type ty -> ty -> nat -> nat -> Prop.
(pretty much done!)
First argument: o : "observer label"
    - If t <= o, then type_rel o t v1 v2
    - Otherwise: type_rel o t1 v1 v2 <-> old_type_rel Sec v1 v2
*)


    
    