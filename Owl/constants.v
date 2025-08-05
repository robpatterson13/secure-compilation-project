Require Import FunctionalExtensionality.

(* Probablity code *)
Inductive Dist A :=
    | Ret : A -> Dist A
    | Flip : ( bool -> Dist A) -> Dist A.

Check Ret.

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

Record Lattice := {
  labels : Set;
  leq : labels -> labels -> bool;
  bot : labels;
  join : labels -> labels -> labels;
  meet : labels -> labels -> labels;
}.

Axiom L : Lattice. 
