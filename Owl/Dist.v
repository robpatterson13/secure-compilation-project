Require Import FunctionalExtensionality.
Require Import QArith.
Require Import List.

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

Lemma flip_unused {A} (c : Dist A) : 
    (_ <- flip ;; c) ~= c.
    intro k.
    simpl.
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
Proof.
  intro f.
  revert c.
  induction d; intro c.
  - simpl. reflexivity.
  - simpl. 
    specialize (H false c) as Hf.
    specialize (H true c) as Ht. 
    rewrite <- Ht.
    rewrite <- Hf.
    induction c.
    + simpl. reflexivity.
    + simpl.
      specialize (H0 false) as IHf.
      specialize (H0 true)  as IHt. 
      rewrite IHf.
      rewrite IHt. field. 
      specialize (H false (d0 true)) as H'. assumption.
      specialize (H true (d0 true)) as H'. assumption.
      specialize (H false (d0 false)) as H'. assumption.
      specialize (H true (d0 false)) as H'. assumption.
Qed.
    

Fixpoint inSupport {A} (c : Dist A) (x : A) :=
  match c with 
  | Ret y => x = y
  | Flip f => inSupport (f false) x \/ inSupport (f true) x end.
  
Definition valid {A} (c : Dist A) (P : A -> Prop) :=
  forall x, inSupport c x -> P x.
  
(* TODO make this work

Notation "|= c { P } " := (valid c P) (at level 60).
*)

Lemma eqDist_cong_l {A B} (c d : Dist A) (k : A -> Dist B) : 
  c ~= d ->
  (x <- c ;; k x) ~= (x <- d ;; k x).
Admitted.
    
Lemma eqDist_cong_r {A B} (c : Dist A) (k1 k2 : A -> Dist B) : 
  (forall x, inSupport c x -> k1 x ~= k2 x) ->
  (x <- c ;; k1 x) ~= (x <- c ;; k2 x).
Proof.
  intros. intro f.
  induction c.
  - simpl. specialize (H a).
    simpl in H. unfold eqDist in H.
    specialize (H) as H'. apply H'.
    reflexivity.
  - simpl. simpl in H. 
    rewrite H0.
    rewrite H0.
    field.
    + intros. apply H. right. assumption.
    + intros. apply H. left. assumption.
Qed.  


Lemma valid_bind {A B} (c : Dist A) P (k : A -> Dist B) Q :
  valid c P -> 
  (forall x, P x -> valid (k x) Q) ->
  valid (x <- c ;; k x) Q.
Proof.
  intros.
  induction c.
  - simpl. apply H0. unfold valid in H.
    specialize (H a). simpl in H. apply H. reflexivity.
  - simpl. unfold valid. intros. unfold valid in H1. simpl in H2.
    specialize (H1 true) as Ht.
    specialize (H1 false) as Hf.
    destruct H2.
    apply Hf.
    + intros. unfold valid in H. specialize (H x0). simpl in H. apply H.
      left. assumption.
    + assumption.
    + apply Ht. intros. unfold valid in H. specialize (H x0). simpl in H. apply H.
      right. assumption. assumption.
Qed.

Lemma valid_ret {A} (x : A) P :
  P x ->
  valid (ret x) P.
Proof.
  intros.
  unfold valid.
  intros.
  unfold inSupport in H0.
  rewrite H0.
  apply H.
Qed.

Lemma valid_flip P : 
  P false ->
  P true ->
  valid flip P.
Proof.
  intros.
  unfold flip.
  unfold valid.
  intros.
  destruct x.
  - apply H0.
  - apply H.
Qed. 




