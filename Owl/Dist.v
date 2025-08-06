From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import QArith.
From Stdlib Require Import Classes.DecidableClass.
From Stdlib Require Import List.

Inductive Dist A :=
    | Ret : A -> Dist A
    | Flip : (bool -> Dist A) -> Dist A.

Arguments Ret [A].
Arguments Flip [A].

Fixpoint bind {A B} (c : Dist A) (k : A -> Dist B) : Dist B :=
    match c with 
    | Ret x => k x
    | Flip f => Flip (fun x => bind (f x) k)
    end.

Definition flip : Dist bool := Flip (fun x => Ret x).

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 100, c1 at next level, right associativity).

Notation "'ret' x" := (Ret x)
  (at level 100).

Lemma bindA {A B C} (c : Dist A) (k : A -> Dist B) (k' : B -> Dist C) : 
    (y <- (x <- c ;; k x);; k' y) =
    (x <- c ;; y <- k x ;; k' y).
    induction c; simpl.
    auto.
    f_equal.
    apply functional_extensionality; intro; eauto.
Qed.

Open Scope Q_scope.

Fixpoint evalDist {A} (c : Dist A) (k : A -> Q) : Q  :=
    match c with 
    | Ret x => k x
    | Flip f => (evalDist (f false) k) / 2 + (evalDist (f true) k) / 2
    end.

Definition eqDist {A} (c d : Dist A) :=
    forall x, 
        evalDist c x == evalDist d x.

Infix "~=" := eqDist (at level 70).

Lemma flip_unused {A} (x : A) : 
    (_ <- flip ;; ret x) ~= (ret x).
    intro; simpl.
    field.
Qed.

Lemma evalDist_bind {A B} (c : Dist A) (k : A -> Dist B) f :
    evalDist (x <- c ;; k x) f ==
    evalDist c (fun x => evalDist (k x) f).
    revert f; 
    induction c.
    simpl; reflexivity.
    simpl; intros.
    rewrite H.
    rewrite H.
    field.
Qed.



Lemma swap_bind {A B C} (c : Dist A) (d : Dist B) (k : A -> B -> Dist C) :
    (x <- c ;; y <- d ;; k x y)
    ~=
    (y <- d ;; x <- c ;; k x y).
Admitted. 

Fixpoint inSupport {A} (c : Dist A) (x : A) :=
  match c with 
  | Ret y => x = y
  | Flip f => inSupport (f false) x \/ inSupport (f true) x end.


Lemma eqDist_cong_l {A B} (c d : Dist A) (k : A -> Dist B) : 
  c ~= d ->
  (x <- c ;; k x) ~= (x <- d ;; k x).
Admitted.

Lemma eqDist_cong_r {A B} (c : Dist A) (k1 k2 : A -> Dist B) : 
  (forall x, inSupport c x -> k1 x ~= k2 x) ->
  (x <- c ;; k1 x) ~= (x <- c ;; k2 x).
Admitted.