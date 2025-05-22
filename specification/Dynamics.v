Require Import String List.
Import ListNotations.

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

Section LatticeSection.
  Variable (L : Lattice).

Inductive value : Type :=
| VNat : nat -> value
| VBool : bool -> value.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_val : value -> tm
| tm_bin_and : tm -> tm -> tm
| tm_bin_add : tm -> tm -> tm
| tm_bin_or : tm -> tm -> tm
| tm_un_not : tm -> tm
| tm_let : string -> tm -> tm -> tm
| tm_declass : tm -> L.(carrier) -> tm
| tm_if : tm -> tm -> tm -> tm.

Fixpoint subst (x : string) (s : value) (t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb x y then tm_val s else t
  | tm_val _ => t 
  | tm_bin_and t1 t2 => tm_bin_and (subst x s t1) (subst x s t2)
  | tm_bin_add t1 t2 => tm_bin_add (subst x s t1) (subst x s t2)
  | tm_bin_or t1 t2 => tm_bin_or (subst x s t1) (subst x s t2)
  | tm_un_not t1 => tm_un_not (subst x s t1)
  | tm_let x_b e b =>
      let body := if String.eqb x x_b then b else (subst x s b) in
      tm_let x_b (subst x s e) body
  | tm_declass t l => tm_declass (subst x s t) l
  | tm_if b t1 t2 => tm_if (subst x s b)  (subst x s t1)  (subst x s t2)
  end.

Definition smap : Type := list (string * value).

Definition trace : Type := list (value * L.(carrier)).

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

Axiom f_un : value -> value.
Axiom f_bin : value -> value -> value.

Definition f_and (v1 v2 : value) : option value :=
  match v1, v2 with
  | VBool b1, VBool b2 => Some (VBool (andb b1 b2))
  | _, _ => None
  end.

Definition f_add (v1 v2 : value) : option value :=
  match v1, v2 with
  | VNat n1, VNat n2 => Some (VNat (n1 + n2))
  | _, _ => None 
  end.

Definition f_or (v1 v2 : value) : option value :=
  match v1, v2 with
  | VBool b1, VBool b2 => Some (VBool (orb b1 b2))
  | _, _ => None
  end.

Definition f_not (v : value) : option value :=
  match v with
  | VBool b => Some (VBool (negb b))
  | _ => None
  end.

Inductive big_eval : tm -> value -> trace -> Prop := 
| Etm_val : forall v,
  big_eval (tm_val v) v []
| Etm_un_not : forall e v v' tr,
  big_eval e v tr -> Some v' = f_not v -> 
  big_eval (tm_un_not e) v' tr
| Etm_bin_and : forall e1 e2 v1 v2 v tr1 tr2,
  big_eval e1 v1 tr1 -> 
  big_eval e2 v2 tr2 -> 
  Some v = f_and v1 v2 -> 
  big_eval (tm_bin_and e1 e2) v (tr1 ++ tr2)
| Etm_bin_add : forall e1 e2 v1 v2 v tr1 tr2,
  big_eval e1 v1 tr1 -> 
  big_eval e2 v2 tr2 -> 
  Some v = f_add v1 v2 -> 
  big_eval (tm_bin_add e1 e2) v (tr1 ++ tr2)
| Etm_bin_or : forall e1 e2 v1 v2 v tr1 tr2,
  big_eval e1 v1 tr1 -> 
  big_eval e2 v2 tr2 -> 
  Some v = f_or v1 v2 -> 
  big_eval (tm_bin_or e1 e2) v (tr1 ++ tr2)
| Etm_let : forall x e1 e2 v1 v2 tr1 tr2,
  big_eval e1 v1 tr1 -> 
  big_eval (subst x v1 e2) v2 tr2 -> 
  big_eval (tm_let x e1 e2) v2 (tr1 ++ tr2)
| Etm_declass : forall e v tr L,
  big_eval e v tr ->
  big_eval (tm_declass e L) v ((v, L) :: tr) 
| Etm_if_true : forall b t1 t2 v1 v2 tr1 tr2 tr3,
  big_eval b (VBool true) tr1 ->
  big_eval t1 v1 tr2 ->
  big_eval t2 v2 tr3 ->
  big_eval (tm_if b t1 t2) v1 (tr1 ++ tr2) 
| Etm_if_false : forall b t1 t2 v1 v2 tr1 tr2 tr3,
  big_eval b (VBool false) tr1 ->
  big_eval t1 v1 tr2 ->
  big_eval t2 v2 tr3 ->
  big_eval (tm_if b t1 t2) v2 (tr1 ++ tr3). 

  Theorem big_eval_det (t : tm) (v1 v2 : value) (tr1 tr2 : trace) : 
  big_eval t v1 tr1 ->
  big_eval t v2 tr2 ->
  v1 = v2.
  intros h1; revert v2 tr2.
  induction h1.
  {
    intros v2 tr2 h2.
    inversion h2.
    reflexivity.
  }
  {
    intros v2 tr2 h2.
    subst.
    inversion h2; subst.
    apply IHh1 in H1 as ->.
    rewrite <- H in H2.  
    inversion H2; subst.
    reflexivity.
  }
  {
    intros v3 tr3 h3.
    subst.
    inversion h3; subst.
    apply IHh1_1 in H2 as ->.
    apply IHh1_2 in H3 as ->.
    rewrite <- H in H6.  
    inversion H6; subst.
    reflexivity.
  }
  {
    intros v3 tr3 h3.
    subst.
    inversion h3; subst.
    apply IHh1_1 in H2 as ->.
    apply IHh1_2 in H3 as ->.
    rewrite <- H in H6.  
    inversion H6; subst.
    reflexivity.
  }
  {
    intros v3 tr3 h3.
    subst.
    inversion h3; subst.
    apply IHh1_1 in H2 as ->.
    apply IHh1_2 in H3 as ->.
    rewrite <- H in H6.  
    inversion H6; subst.
    reflexivity.
  }
  {
    intros v0 tr0 h.
    inversion h; subst; clear h.
    specialize (IHh1_1 _ _ H4); subst.
    specialize (IHh1_2 _ _ H5).
    apply IHh1_2.
  }
  {
    intros v2 tr2 h2.
    inversion h2; subst.
    specialize (IHh1 _ _ H3); subst.
    reflexivity.
  }
  {
    intros v3 tr_2 h2.
    inversion h2; subst.
    - specialize(IHh1_2 v3 tr4 H5).
      apply IHh1_2.
    - specialize (IHh1_1 (VBool false) tr0 H2).
      discriminate.
  }
  {
    intros v3 tr_2 h2.
    inversion h2; subst.
    - specialize (IHh1_1 (VBool true) tr0 H2).
      discriminate.
    - specialize(IHh1_3 v3 tr5 H6).
      apply IHh1_3.
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

Lemma subst_many_tm_bin_and g e1 e2 : 
  subst_many g (tm_bin_and e1 e2) = 
    tm_bin_and (subst_many g e1) (subst_many g e2).
  revert e1 e2. 
  induction g.
  simpl; reflexivity.
  simpl.
  destruct a.
  intros e1 e2.
  rewrite IHg; reflexivity.
Qed.

Lemma subst_many_tm_bin_or g e1 e2 : 
  subst_many g (tm_bin_or e1 e2) = 
    tm_bin_or (subst_many g e1) (subst_many g e2).
  revert e1 e2. 
  induction g.
  simpl; reflexivity.
  simpl.
  destruct a.
  intros e1 e2.
  rewrite IHg; reflexivity.
Qed.

Lemma subst_many_if g b e1 e2 : 
  subst_many g (tm_if b e1 e2) = 
    tm_if (subst_many g b) (subst_many g e1) (subst_many g e2).
  revert b e1 e2. 
  induction g.
  simpl; reflexivity.
  simpl.
  destruct a.
  intros b e1 e2.
  rewrite IHg; reflexivity.
Qed.

Lemma subst_many_tm_bin_add g e1 e2 : 
  subst_many g (tm_bin_add e1 e2) = 
    tm_bin_add (subst_many g e1) (subst_many g e2).
  revert e1 e2. 
  induction g.
  simpl; reflexivity.
  simpl.
  destruct a.
  intros e1 e2.
  rewrite IHg; reflexivity.
Qed.

Lemma subst_many_un_not : forall g u, 
  subst_many g (tm_un_not u) = tm_un_not (subst_many g u).
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

Lemma subst_many_declass: forall g t l,
  subst_many g (tm_declass t l) = tm_declass (subst_many g t) l.
  intros g.
  induction g; simpl.
  -intros t l. reflexivity.
  -intros t l. destruct a.
   rewrite IHg.
   reflexivity.
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
  forall (x s : string) (v n : value) (e : tm),
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
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite IHe1. rewrite IHe2. reflexivity.
  - rewrite IHe; reflexivity.
  - rewrite IHe1.
    destruct (String.eqb s s0); simpl.
    + reflexivity.
    + rewrite IHe2; reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
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
  forall (x s : string) (v n : value) (e : tm),
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
  - simpl; rewrite IHe1; rewrite IHe2; reflexivity.
  - simpl; rewrite IHe1; rewrite IHe2; reflexivity.
  - simpl; rewrite IHe; reflexivity.
  - simpl; rewrite IHe1.
    destruct (String.eqb x s0); destruct (String.eqb s s0); subst; try reflexivity.
    + simpl; rewrite IHe2; reflexivity.
  -simpl. rewrite IHe. reflexivity.
  -simpl. rewrite IHe1. rewrite IHe2. rewrite IHe3. reflexivity.
Qed.

Lemma subst_many_subst_commute:
  forall (x : string) (v : value) (g : smap) (e : tm),
    (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst x v e))
    = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) e)).
  induction g; simpl.
  - reflexivity.
  - destruct a; simpl; destruct (negb (String.eqb s x)) eqn:H_s_x; simpl.
    + intro e.
      apply Bool.negb_true_iff in H_s_x. apply String.eqb_neq in H_s_x.
      apply id_neq_sym in H_s_x.
      rewrite (subst_neq_id_commute x s v v0 e H_s_x).
      rewrite (IHg (subst s v0 e)).
      reflexivity.
    + apply IHg.
Qed.

End LatticeSection.