From Coq Require Import Strings.String.
Require Import List.
Import ListNotations .
Require Import Dynamics.

Inductive ty := 
  | Pub
  | Middle
  | Sec.

Scheme Equality for ty.

Section Types.
  Variable (L : Lattice).

Inductive type : Type :=
| nat_L : L.(carrier) -> type
| bool_L : L.(carrier) -> type.

Definition context : Type := list (string *  (type)). 

Inductive has_type : context -> tm L -> type -> Prop :=
| T_Var : forall Gamma x t1,
    lookup Gamma x = Some t1 ->
    has_type Gamma (tm_var L x) t1
| T_Val_Nat : forall Gamma v,
    has_type Gamma (tm_val L (VNat v)) (nat_L L.(bot))
| T_Val_Bool : forall Gamma b,
    has_type Gamma (tm_val L (VBool b)) (bool_L L.(bot))
| T_Un_Not : forall Gamma e l,
    has_type Gamma e (bool_L l) ->
    has_type Gamma (tm_un_not L e) (bool_L l)
| T_Bin_And : forall Gamma e1 e2 l1 l2,
    has_type Gamma e1 (bool_L l1) ->
    has_type Gamma e2 (bool_L l2) ->
    has_type Gamma (tm_bin_and L e1 e2) (bool_L (L.(max) l1 l2))
| T_Bin_Add : forall Gamma e1 e2 l1 l2,
    has_type Gamma e1 (nat_L l1) ->
    has_type Gamma e2 (nat_L l2) ->
    has_type Gamma (tm_bin_add L e1 e2) (nat_L (L.(max) l1 l2))
| T_Let : forall Gamma e1 e2 x t1 t2,
    has_type Gamma e1 t1 ->
    has_type (update Gamma x t1) e2 t2 ->
    has_type Gamma (tm_let L x e1 e2) t2
| T_Declass_Nat : forall Gamma e l Label,
    has_type Gamma e (nat_L l) ->
    has_type Gamma (tm_declass L e Label) (nat_L Label)
| T_Declass_Bool : forall Gamma e l Label,
    has_type Gamma e (bool_L l) ->
    has_type Gamma (tm_declass L e Label) (bool_L Label).

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
    