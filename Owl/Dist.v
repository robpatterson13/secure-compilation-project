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
      rewrite IHt.
      field. 
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
  

Notation "|= c { P }" := (valid c P) (at level 60, c at level 0, P at level 0).

Lemma eqDist_cong_l {A B} (c d : Dist A) (k : A -> Dist B) : 
  c ~= d ->
  (x <- c ;; k x) ~= (x <- d ;; k x).
Proof.
  intros.
  intro f.
  repeat rewrite evalDist_bind.
  apply H.
Qed.
    
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
  |= c { P } -> 
  (forall x, P x -> |= (k x) {Q}) ->
  |= (x <- c ;; k x) {Q}.
Proof.
  intros.
  induction c.
  - simpl. apply H0.  unfold valid in H.
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
  |= (ret x) { P }.
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
  |= flip { P }.
Proof.
  intros.
  unfold flip.
  unfold valid.
  intros.
  destruct x.
  - apply H0.
  - apply H.
Qed. 

Lemma valid_flip_gen P : 
  forall f,
    P false ->
    P true ->
    |= (Flip f) { P }.
Proof.
  intros.
  unfold valid.
  intros.
  destruct x.
  - apply H0.
  - apply H.
Qed.

Fixpoint uniform_bind_core {A B}
         (c : Dist A) (k : A -> option (Dist B)) : option (Dist B) :=
  match c with
  | Ret x => k x
  | Flip f =>
      match uniform_bind_core (f false) k,
            uniform_bind_core (f true)  k with
      | Some d1, Some d2 => Some (Flip (fun b => if b then d2 else d1))
      | _, _ => None
      end
  end.

Definition uniform_bind {A B}
           (co : option (Dist A)) (k : A -> option (Dist B)) : option (Dist B) :=
  match co with
  | None => None
  | Some c => uniform_bind_core c k
  end.

Definition inSupportUniform {A} (c : option (Dist A)) (x : A) :=
  match c with 
  | None => False
  | Some c' => (inSupport c' x) end.

Lemma uniform_bind_ext_on {A B}
  (d : option (Dist A)) (K1 K2 : A -> option (Dist B)) :
  (forall x, inSupportUniform d x -> K1 x = K2 x) ->
  uniform_bind d K1 = uniform_bind d K2.
Proof.
  intros. destruct d.
  induction d.
  - simpl. specialize (H a).
    simpl in H. apply H. reflexivity.
  - simpl in H. specialize (H0 false) as Hf. specialize (H0 true) as Ht. simpl.
    specialize (Hf (fun x hx => H x (or_introl hx))) as Ef1. (* VERY USEFUL TOOLS *)
    specialize (Ht (fun x hx => H x (or_intror hx))) as Et1.
    unfold uniform_bind in Ef1. unfold uniform_bind in Et1.
    rewrite Ef1. rewrite Et1. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma uniform_bind_all_some {A B} (c : option (Dist A)) (k : A -> option (Dist B)) d' :
  uniform_bind c k = Some d' ->
  forall x, inSupportUniform c x -> exists d'', k x = Some d''.
Proof.
  revert k d'.
  destruct c.
  induction d; intros k d' Hb x Hsup; simpl in *.
  - subst. eexists. exact Hb.
  - destruct (uniform_bind_core (d false) k) eqn:Hf0;
    destruct (uniform_bind_core (d true)  k) eqn:Hf1;
    try discriminate Hb.
    inversion Hb; subst; clear Hb.
    destruct Hsup.
    + eapply H. apply Hf0. assumption.
    + eapply H. apply Hf1. assumption.
  - intros. simpl. inversion H0; subst.
Qed. 

Definition coupling {A} {B} (R : A -> B -> Prop) (d1 : Dist A) (d2 : Dist B) :=
{c : Dist (A * B) | 
    d1 ~= (x <- c ;; Ret (fst x)) /\
    d2 ~= (x <- c ;; Ret (snd x)) /\
    |= c { fun '(x, y) => R x y } }.

Notation "|= c ~ d { P }" := (coupling P c d) (at level 60, d at level 0, c at level 0, P at level 0).

Lemma coupling_refl {A} (d : Dist A) : 
  |= d ~ d { eq }.
Proof.
  unfold coupling.
  exists (x <- d;; (ret (x, x))).
  split.
  unfold eqDist.
  intros.
  rewrite evalDist_bind. rewrite evalDist_bind. simpl. reflexivity.
  split.
  unfold eqDist. intros.
  rewrite evalDist_bind. rewrite evalDist_bind. simpl. reflexivity.
  unfold valid.
  intros.
  destruct x.
  induction d.
  - simpl in H. inversion H; subst. reflexivity.
  - simpl in H. destruct H.
    + specialize (H0 false H). apply H0.
    + specialize (H0 true H). apply H0.
Qed.

Lemma coupling_flip_opp :
  coupling (fun x y => x = negb y) flip flip.
Proof.
  unfold coupling.
  exists (Flip (fun x => (Ret (x, (negb x))))).
  split.
  simpl. unfold flip. unfold eqDist. intros. simpl. reflexivity.
  split.
  simpl. unfold flip. unfold eqDist. intros. simpl. field.
  unfold valid. intros. unfold inSupport in H. destruct H.
  inversion H; subst. simpl. reflexivity.
  inversion H; subst. simpl. reflexivity.
Qed.

Lemma coupling_eq {A} (d1 d2 : Dist A) : 
  coupling eq d1 d2 -> 
  d1 ~= d2.
Proof.
  intros.
  unfold eqDist. unfold coupling in X.
  destruct X. destruct a. destruct H0.
  intros. 
  unfold eqDist in H. specialize (H x0).
  unfold eqDist in H0. specialize (H0 x0).
  rewrite H. rewrite H0. 
  unfold valid in H1. 
  apply eqDist_cong_r.
  intros.
  specialize (H1 x1 H2).
  destruct x1.
  simpl.
  rewrite H1.
  unfold eqDist.
  intros.
  reflexivity.
Qed.

(* Fixpoint dbind {A B} (c : Dist A) (k : forall x, inSupport c x -> Dist B) : Dist B.
  destruct c.
  simpl in k.
  apply (k a eq_refl).
  simpl in *.
  refine (Flip (fun b => dbind _ _ (d b) (fun x h => k x _))).
  destruct b.
  right; apply h.
  left; apply h.
Defined.

Lemma coupling_bind {A B C D} (d1 : Dist A) (d2 : Dist B) (k1 : A -> Dist C) (k2 : B -> Dist D) r1 r2 : 
  coupling r1 d1 d2 ->
  (forall x y, r1 x y -> coupling r2 (k1 x) (k2 y)) ->
  coupling r2 (x <- d1 ;; k1 x) (x <- d2 ;; k2 x).
  intros.
  assert (H : forall x, inSupport (proj1_sig X) x -> r1 (fst x) (snd x)).
  destruct X.
  destruct a.
  destruct a.
  simpl.
  intros.
  specialize (v x0).
  simpl in v.
  destruct x0; simpl in *.
  apply v; auto.

  exists (dbind (proj1_sig X) (fun '(x, y) h => proj1_sig (X0 x y (H (x, y) h)))).
Admitted. *)

(* TODO: the natural rule for bind: if |= c1 ~ c2 { R }, and if forall x and y,  
  R x y implies |= (k1 x) ~ (k2 y) { Q }, then 
  |= (x <- c1 ;; k1 x) ~ (y <- c2 ;; k2 x) { Q }.
*)




