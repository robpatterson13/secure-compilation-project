From Coq Require Import Strings.String.
Require Import List.
Import ListNotations.

Inductive tm : Type :=
| tm_var : string -> tm
| tm_val : nat -> tm
| tm_bin : tm -> tm -> tm
| tm_un : tm -> tm
| tm_let : string -> tm -> tm -> tm.

Inductive ty : Type :=
| Pub : ty
| Sec : ty.

Fixpoint subst (x : string) (s : nat) (t : tm) : tm :=
  match t with
  | tm_var y => if String.eqb x y then tm_val s else t
  | tm_val _ => t 
  | tm_bin t1 t2 => tm_bin (subst x s t1) (subst x s t2)
  | tm_un t1 => tm_un (subst x s t1)
  | tm_let x_b e b =>
      let body := if String.eqb x_b x then b else (subst x s b) in
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

Definition max (t1 : ty) (t2 : ty) :=
  match t1, t2 with
  | Pub, Pub => Pub
  | Pub, Sec => Sec
  | Sec, Pub => Sec
  | Sec, Sec => Sec
  end.

Definition context : Type := list (string * ty).

Definition update (Gamma : context) (x : string) (t : ty) : context :=
  (x, t) :: Gamma.

Fixpoint lookup {A} (m : list (string * A)) (x : string) : option A :=
  match m with
  | [] => None
  | (y, t) :: m' =>
      if String.eqb x y then Some t
      else lookup m' x
  end.

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

Inductive type_rel : ty -> nat -> nat -> Prop :=
| TR_Pub : forall v,
  type_rel Pub v v
| TR_Sec : forall v1 v2,
  type_rel Sec v1 v2.

Definition type_rel_2 (t : ty) (v1 v2 : nat) :=
  match t with
    | Pub => v1 = v2 
    | Sec => True end.
                        

Definition subst_rel : context -> smap -> smap -> Prop :=
  fun G g1 g2 =>
    forall (x : string),
      match lookup G x, lookup g1 x, lookup g2 x with
        | None, _, _ => True
        | Some t, Some v1, Some v2 => 
            type_rel t v1 v2
        | Some t, _, _ => False end.
            

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


Definition has_sem_type : context -> tm -> ty -> Prop  :=
  fun Gamma e t =>
    forall g1 g2 v1 v2,
      subst_rel Gamma g1 g2 ->
      big_eval (subst_many g1 e) v1 ->
      big_eval (subst_many g2 e) v2 ->
      type_rel t v1 v2.

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

(*Lemma subst_many_let : forall g id e b,
    subst_many g (tm_let id e b) = *)

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

Theorem noninterference G e t :
  has_type G e t ->
  has_sem_type G e t.
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
    apply TR_Pub.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h1 h2 h3.
    rewrite subst_many_un in h2.
    rewrite subst_many_un in h3.
    inversion h2; subst.
    inversion h3; subst.

    destruct (IHh g1 g2 v v0 h1 H0 H1); subst; constructor.
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
      constructor.
    - simpl.
      destruct t2; constructor.
  }
  {
    unfold has_sem_type.
    intros g1 g2 v1 v2 h_sub h_eval1 h_eval2.
    admit.
  }
Admitted.
      
    
    
