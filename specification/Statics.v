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
(* TODO 1 : new max function *)

(*
  match t1, t2 with
  | Pub, Pub => Pub
  | Pub, Sec => Sec
  | Sec, Pub => Sec
  | Sec, Sec => Sec
  end.
*)

(* TODO 2 : define this directly *)
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
(* TODO: prove that le is a partial order *)
(* - Reflexive *)
(* - Transitive *)

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

First argument: o : "observer label"
    - If t <= o, then type_rel o t v1 v2
    - Otherwise: type_rel o t1 v1 v2 <-> old_type_rel Sec v1 v2
*)


Inductive type_rel : ty -> ty -> nat -> nat -> Prop :=
  | TR_Low : forall o t v, 
      type_rel o t v v
  | TR_High : forall o t v1 v2,
      le t o = false -> 
      type_rel o t v1 v2.


(* TODO: adapt for type_rel *)
Definition subst_rel (o : ty) : context -> smap -> smap -> Prop :=
  fun G g1 g2 =>
    forall (x : string),
      match lookup G x, lookup g1 x, lookup g2 x with
        | None, _, _ => True
        | Some t, Some v1, Some v2 => 
            type_rel o t v1 v2
        | Some t, _, _ => False end.
            
Definition has_sem_type (o : ty) : context -> tm -> ty -> Prop  :=
  fun Gamma e t =>
    forall g1 g2 v1 v2,
      subst_rel o Gamma g1 g2 ->
      big_eval (subst_many g1 e) v1 ->
      big_eval (subst_many g2 e) v2 ->
      type_rel o t v1 v2.

(* TODO: Dynamics.v *)
Lemma subst_many_val g v : 
  subst_many g (tm_val v) = tm_val v.
  induction g.
  simpl.
  reflexivity.
  simpl.
  
  destruct a.
  apply IHg.
Qed.

(* TODO: Dynamics.v *)
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

(* TODO: Dynamics.v *)
Lemma subst_many_let : forall g id e b,
    subst_many g (tm_let id e b) = tm_let id (subst_many g e) (subst_many (filter (fun x => negb (String.eqb (fst x) id)) g) b).
  intros g id.
  induction g; simpl.
  - reflexivity.
  - destruct a; simpl.
    destruct (String.eqb s id); simpl;
      intros e b; apply IHg.
Qed.

(* TODO: Dynamics.v *)
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

(* TODO: Dynamics.v *)
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

(* TODO: Dynamics.v *)
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

(* ------ Fix here -------- *) 

Lemma subst_rel_update:
  forall (o t : ty) (Gamma : context) (g1 g2 : smap) (x : string) (v1 v2 : nat),
    type_rel o t v1 v2 ->
    subst_rel o Gamma g1 g2 ->
    subst_rel o (update Gamma x t)
      (update g1 x v1)
      (update g2 x v2).
  intros.
  unfold subst_rel.
  intro. 
  unfold update. 
  simpl. 
  destruct (x0 =? x)%string eqn:H_string.
  {
    apply H. 
  }
  {
    unfold subst_rel in H0.
    apply H0.
  }  
Qed.

Definition filter_smap (g : smap) (x : string) : smap :=
  filter (fun y => negb (String.eqb (fst y) x)) g.
    

Lemma lookup_filter:
  forall (g : smap) (x1 x2 : string),
  (x1 =? x2)%string = false
  -> lookup(filter_smap g x2) x1 = lookup g x1.
Proof.
intros.
induction g.
{
  auto.
}
{
  simpl.
  destruct a.
  simpl.
  destruct (s =? x2)%string eqn:H_x2.
  {
    
    destruct (x1 =? x2)%string eqn:H_x1.
    {
      discriminate. 
    }
    {
      simpl.
      apply String.eqb_eq in H_x2. 
      subst s.
      rewrite H_x1.
      apply IHg. 
    }
  }
  {
    simpl. destruct (x1 =? s)%string eqn:H_x1.
    {
     auto. 
    }
    {
      apply IHg. 
    } 
  }
}
Qed.
  

Lemma subst_rel_after_update:
  forall (Gamma : context) (g1 g2 : smap) (x : string) (v1 v2 : nat) (o t : ty),
    type_rel o t v1 v2 ->
    subst_rel o Gamma g1 g2 ->
    subst_rel o (update Gamma x t)
      (update (filter_smap g1 x) x v1)
      (update (filter_smap g2 x) x v2).
  intros.
  intro.
  unfold update.
  simpl.
  destruct (x0 =? x)%string eqn:h.
  auto.
  destruct (lookup Gamma x0) eqn:h'; auto.
  destruct (lookup (filter_smap g1 x) x0) eqn:h''.
  destruct (lookup (filter_smap g2 x) x0) eqn:h'''.
  specialize(H0 x0).
  rewrite h' in H0.
  {
    pose proof (lookup_filter g1 x0 x) as h_f1.
    pose proof (lookup_filter g2 x0 x) as h_f2.
    rewrite h in h_f1; rewrite h in h_f2.
    specialize (h_f1 eq_refl).
    specialize (h_f2 eq_refl).
    rewrite h_f1 in h''.
    rewrite h_f2 in h'''.
    rewrite h'' in H0.
    rewrite h''' in H0.
    apply H0.
  }
  {
  unfold subst_rel in H0.
  specialize(H0 x0).
  rewrite h' in H0.
  pose proof (lookup_filter g1 x0 x) as h_f1.
  pose proof (lookup_filter g2 x0 x) as h_f2.
  rewrite h in h_f1; rewrite h in h_f2.
  specialize (h_f1 eq_refl).
  specialize (h_f2 eq_refl).
  rewrite h_f1 in h''.
  rewrite h_f2 in h'''.
  rewrite h'' in H0.
  rewrite h''' in H0.
  apply H0.
  }
  {
  unfold subst_rel in H0.
  specialize(H0 x0).
  rewrite h' in H0.
  pose proof (lookup_filter g1 x0 x) as h_f1.
  pose proof (lookup_filter g2 x0 x) as h_f2.
  rewrite h in h_f1; rewrite h in h_f2.
  specialize (h_f1 eq_refl).
  specialize (h_f2 eq_refl).
  rewrite h_f1 in h''.
  rewrite h'' in H0.
  apply H0.
  }
Qed.



(* TODO: write the rest of subst_many lemmas, AFTER looking at the main proof *)
  
(*
  - simpl, simpl at *
  - subst
  - rewrite H at H2, or just rewrite H
  - apply H
  - inversion H, if H is an inductive prop
  - intros and revert
  - assert (h : ...) with { } 
  - destruct
  - writing and applying sub-lemmas
*)

(*
  - If your inductive hypothesis doesn't match up, consider calling revert to generalize before inducting 

*)

(* TODO: make it still work *)
(* TODO: add the observer label *)
Theorem noninterference o G e t :
  has_type G e t ->
  has_sem_type o G e t.
  intros h.
  induction h.
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 Hv1 Hv2.
    specialize (h1 x).
    destruct (lookup g1 x) eqn:E1; [ | (rewrite H in h1; contradiction) ].
    destruct (lookup g2 x) eqn:E2; [ | (rewrite H in h1; contradiction) ].
    rewrite (subst_many_var g1 x) in Hv1; rewrite E1 in Hv1; simpl in Hv1.
    rewrite (subst_many_var g2 x) in Hv2; rewrite E2 in Hv2; simpl in Hv2.
    inversion Hv1; subst.
    inversion Hv2; subst.
    rewrite H in h1.
    exact h1.    
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 h2 h3.
    rewrite subst_many_val in h2.
    rewrite subst_many_val in h3.
    inversion h2; subst.
    inversion h3; subst.
    apply TR_Low.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 h2 h3.
    rewrite subst_many_un in h2.
    rewrite subst_many_un in h3.
    inversion h2; subst.
    inversion h3; subst.

    destruct (IHh g1 g2 v v0 h1 H0 H1); subst; constructor.
    apply H.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h_sub h_eval1 h_eval2.
    rewrite subst_many_tm_bin in h_eval1.
    rewrite subst_many_tm_bin in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.

    destruct (IHh1 g1 g2 v0 v1 h_sub H1 H3); subst.
    destruct (IHh2 g1 g2 v3 v4 h_sub H2 H4); subst.
    - simpl.
      constructor.
    - simpl.
      constructor. destruct t; destruct t0; try apply H; unfold max; destruct o; auto.
    -simpl.
     constructor. destruct t; destruct t2; try apply H; unfold max; destruct o; try auto.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h_sub h_eval1 h_eval2.
    rewrite subst_many_let in h_eval1.
    rewrite subst_many_let in h_eval2.
    inversion h_eval1; subst.
    inversion h_eval2; subst.

    unfold has_sem_type in IHh2.
    specialize (IHh2 (update (filter (fun y => negb (String.eqb (fst y) x)) g1) x v0) (update (filter (fun y => negb (String.eqb (fst y) x)) g2) x v3) v1 v2).  
            
    (* want to generalize following assertions as lemmas over
       arbitrary gammas without x *)        
    assert (H_pull_out_inner_subst : forall x v s n e g,
               x <> s ->
               (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst s n (subst x v e)))
               = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) (subst s n e)))). {
      intros.
      induction g; simpl.
      - apply (subst_neq_id_commute x0 s v n e).
        exact H.
      - destruct a; simpl; destruct (String.eqb s0 x0) eqn:H_s0_x0; simpl.
        + apply IHg.
        + rewrite (subst_neq_id_commute x0 s v n e).
          rewrite (subst_neq_id_commute x0 s0 v n0 (subst s n e)).
          apply (subst_many_subst_commute x0 v g (subst s0 n0 (subst s n e))).
          apply String.eqb_neq in H_s0_x0.
          apply id_neq_sym in H_s0_x0; exact H_s0_x0.
          exact H.
    }
    
    assert (H_update_subst_equiv : forall g v e,
               (subst_many (update (filter (fun y => negb (String.eqb (fst y) x)) g) x v) e)
               = (subst x v (subst_many (filter (fun y => negb (String.eqb (fst y) x)) g) e))). {
      simpl.
      induction g; simpl.
      - reflexivity.
      - destruct a; simpl.
        destruct (negb (String.eqb s x)) eqn:H_eq; simpl.
        + apply Bool.negb_true_iff in H_eq; apply String.eqb_neq in H_eq.
          intros v e; specialize (H_pull_out_inner_subst x v s n e g); auto.
        + apply IHg.
    }
    
    rewrite (H_update_subst_equiv g1 v0 e2) in IHh2.
    rewrite (H_update_subst_equiv g2 v3 e2) in IHh2.
    
    unfold has_sem_type in IHh1.
    apply IHh2.
    apply subst_rel_after_update.
    eapply IHh1.
    apply h_sub.
    apply H3.
    apply H5.
    apply h_sub.
    apply H4.
    apply H6.
    }
Qed.
    
    