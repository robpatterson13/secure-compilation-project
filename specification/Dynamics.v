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

Lemma subst_many_val g v : 
  subst_many g (tm_val v) = tm_val v.
  induction g.
  simpl.
  reflexivity.
  simpl.
  
  destruct a.
  apply IHg.
Qed.

Lemma subst_many_tm_bin g e1 e2 : 
  subst_many g (tm_bin e1 e2) = 
    tm_bin (subst_many g e1) (subst_many g e2).
  revert e1 e2. 
  induction g.
  simpl; reflexivity.
  simpl.
  destruct a.
  intros e1 e2.
  rewrite IHg; reflexivity.
Qed.

Lemma subst_many_un : forall g u, 
  subst_many g (tm_un u) = tm_un (subst_many g u).
  intros g. induction g.
  - intros u. simpl. reflexivity.
  - intros u. simpl. 
    destruct a.
    rewrite IHg.
    reflexivity.
Qed.

Lemma subst_many_let : forall g id e b,
    subst_many g (tm_let id e b) = tm_let id (subst_many g e) (subst_many (filter (fun x => negb (String.eqb (fst x) id)) g) b).
  intros g id.
  induction g; simpl.
  - reflexivity.
  - destruct a; simpl.
    destruct (String.eqb s id); simpl;
      intros e b; apply IHg.
Qed.

Lemma subst_many_var :
  forall (g : smap) (x : string),
    subst_many g (tm_var x) =
      match lookup g x with
      | None => tm_var x
      | Some n => tm_val n
      end.
Proof.
  intros g x. 
  induction g as [| [y val] g' IH]; simpl.
  - reflexivity.
  - destruct (String.eqb y x) eqn:Heq.
    + apply String.eqb_eq in Heq; subst.
      rewrite subst_many_val. rewrite String.eqb_refl. reflexivity.
    + rewrite <- String.eqb_sym. rewrite Heq. apply IH.
Qed.

Lemma subst_eq_id_erasure:
  forall (x s : string) (v n : nat) (e : tm),
    x = s ->
    (subst s n (subst x v e)) = (subst x v e).
  intros.
  induction e; subst; simpl.
  - destruct (String.eqb s s0) eqn:H_x0_s0; subst; simpl.
    + reflexivity.
    + rewrite H_x0_s0.
      reflexivity.
  - reflexivity.
  - rewrite IHe1; rewrite IHe2; reflexivity.
  - rewrite IHe; reflexivity.
  - rewrite IHe1.
    destruct (String.eqb s s0); simpl.
    + reflexivity.
    + rewrite IHe2; reflexivity.
Qed.

Lemma id_neq_sym:
  forall (a b : string), b <> a -> a <> b.
  intros.
  unfold not.
  unfold not in H.
  intro h_eq; rewrite h_eq in H.
  auto.
Qed.

Lemma subst_neq_id_commute:
  forall (x s : string) (v n : nat) (e : tm),
    x <> s ->
    (subst s n (subst x v e)) = (subst x v (subst s n e)).
  intros.
  induction e; subst.
  - destruct (String.eqb x s) eqn:H_x_s; destruct (String.eqb s s0) eqn:H_s_s0; subst;
      try apply String.eqb_eq in H_x_s; try contradiction.
    + simpl.
      rewrite H_s_s0.
      simpl.
      apply String.eqb_eq in H_s_s0.
      rewrite H_s_s0 in H.
      apply String.eqb_neq in H; rewrite H.
      simpl.
      apply String.eqb_eq in H_s_s0; rewrite H_s_s0.
      reflexivity.
    + simpl.
      rewrite H_s_s0.
      simpl.
      destruct (String.eqb x s0); simpl.
      * reflexivity.
      * rewrite H_s_s0; reflexivity.
  - reflexivity.
  - simpl; rewrite IHe1; rewrite IHe2; reflexivity.
  - simpl; rewrite IHe; reflexivity.
  - simpl; rewrite IHe1.
    destruct (String.eqb x s0); destruct (String.eqb s s0); subst; try reflexivity.
    + simpl; rewrite IHe2; reflexivity.
Qed.

Lemma subst_many_subst_commute:
  forall (x : string) (v : nat) (g : smap) (e : tm),
    (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst x v e))
    = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) e)).
  induction g; simpl.
  - reflexivity.
  - destruct a; simpl; destruct (negb (String.eqb s x)) eqn:H_s_x; simpl.
    + intro e.
      apply Bool.negb_true_iff in H_s_x. apply String.eqb_neq in H_s_x.
      apply id_neq_sym in H_s_x.
      rewrite (subst_neq_id_commute x s v n e H_s_x).
      rewrite (IHg (subst s n e)).
      reflexivity.
    + apply IHg.
Qed.