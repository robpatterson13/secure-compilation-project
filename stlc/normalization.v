Require Import core unscoped stlc.
Require Import List. 
Require Import Setoid Morphisms Relation_Definitions.

Definition context := list ty.

Definition lookup (G : context) (x : nat) : option ty :=
  nth_error G x.

Inductive is_value : tm -> Prop :=
  | v_true : is_value true
  | v_false : is_value false
  | v_lam : forall T t, is_value (lam T t)
  | v_num : forall n, is_value (num n).

Inductive big_eval : tm -> tm -> Prop := 
| E_Val : forall e,
    is_value e ->
    big_eval e e
| E_IfThenElseTrue : forall b e1 e2 v,
    big_eval b true ->
    big_eval e1 v ->
    is_value v ->
    big_eval (ifthenelse b e1 e2) v
| E_IfThenElseFalse : forall b e1 e2 v,
    big_eval b false ->
    big_eval e2 v ->
    is_value v ->
    big_eval (ifthenelse b e1 e2) v
| E_App : forall e1 e2 T t v v2,
    big_eval e1 (lam T t) ->
    big_eval e2 v2 ->
    is_value v2 ->
    big_eval (subst_tm (scons v2 var_tm) t) v ->
    is_value v ->
    big_eval (Core.app e1 e2) v.

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall Gamma x t1,
    lookup Gamma x = Some t1 ->
    has_type Gamma (var_tm x) t1
| T_True : forall Gamma,
    has_type Gamma true bool
| T_False : forall Gamma,
    has_type Gamma false bool
| T_Num : forall Gamma n,
    has_type Gamma (num n) nat_ty
| T_Lam : forall Gamma t1 t2 e,
    has_type (t1 :: Gamma) e t2 ->
    has_type Gamma (lam t1 e) (arr t1 t2)
| T_IfThenElse : forall Gamma t b e1 e2,
    has_type Gamma b bool ->
    has_type Gamma e1 t ->
    has_type Gamma e2 t ->
    has_type Gamma (ifthenelse b e1 e2) t
| T_App : forall Gamma t1 t2 e1 e2,
    has_type Gamma e1 (arr t1 t2) ->
    has_type Gamma e2 t1 ->
    has_type Gamma (Core.app e1 e2) t2.

Fixpoint SN_V (T : ty) (v : tm) : Prop :=
  match T with
  | nat_ty => 
      match v with
      | (num v) => v = 0 \/ (exists n, v = (S n))
      | _ => False
      end
  | bool => v = true \/ v = false
  | (arr t1 t2) =>
      match v with
      | (lam t1' t)  =>
          t1' = t1 /\
          (forall v', SN_V t1 v' ->
          (exists v'', big_eval (subst_tm (scons v' var_tm) t) v'' /\ SN_V t2 v''))
      | _ => False
      end
  end.

Definition SN_E (T : ty) (e : tm): Prop :=
  exists v, big_eval e v /\ SN_V T v.

Inductive SN_G : list ty -> (nat -> tm) -> Prop :=
| G_Empty : SN_G nil ids
| G_Cons : forall Gamma' T o v,
  SN_G Gamma' o ->
  SN_V T v ->
  SN_G (T :: Gamma') (scons v o).

Definition has_sem_type (Gamma : list ty) (e : tm) (t : ty) : Prop :=
  forall (g : nat -> tm),
    SN_G Gamma g ->
    SN_E t (subst_tm g e).

Definition SN (T : ty) (e : tm): Prop :=
  exists v, big_eval e v /\ SN_V T v.

Lemma lookup_nil_none : forall x, lookup nil x = None.
Proof.
  intros x.
  simpl.
  destruct x.
  reflexivity.
  reflexivity.
Qed.

Lemma sn_var :
  forall Gamma g, SN_G Gamma g ->
  forall x t, lookup Gamma x = Some t -> SN_V t (g x).
Proof.
  intros Gamma g HG.
  induction HG; intros x t Hlk; simpl in Hlk.
  - destruct x. (* needed to understand structure of x as a nat *)
    * discriminate. (* 0 *)
    * simpl in Hlk. discriminate. (* n + 1 *)  
  - destruct x; simpl in Hlk.
    * inversion Hlk; subst.               
      asimpl.                             
      exact H.
    * asimpl. apply IHHG. exact Hlk.
Qed.

Lemma SN_V_is_value : forall τ v, SN_V τ v -> is_value v.
Proof.
  induction τ; intros v Hv.
  - destruct Hv; subst; constructor.
  - destruct v; try contradiction.
    constructor.
  - destruct v; try contradiction.
    constructor.
Qed.

Lemma sn_one (Gamma : list ty) (e : tm) (t : ty):
  has_type Gamma e t ->
  has_sem_type Gamma e t.
Proof.
  intros. 
  induction H.
  {
    unfold has_sem_type.
    asimpl.
    intros.
    specialize (sn_var Gamma g H0 x t1 H) as H_var.
    unfold SN_E.
    exists (g x).
    split.
    - specialize (SN_V_is_value t1 (g x) H_var) as S_Val.
      inversion S_Val; subst; constructor; constructor.
    - assumption.
  }
  {
   unfold has_sem_type.
   intros.
   unfold SN_E.
   asimpl.
   exists true.
   split.
   - constructor. constructor.
   - constructor. reflexivity. 
  }
  {
   unfold has_sem_type.
   intros.
   unfold SN_E.
   asimpl.
   exists false.
   split.
   - constructor. constructor.
   - unfold SN_V. right. reflexivity. 
  }
  {
    unfold has_sem_type.
    intros.
    unfold SN_E.
    asimpl.
    exists (num n).
    split.
    - constructor. constructor.
    - unfold SN_V. destruct n.
      * left; reflexivity.
      * right. exists n. reflexivity.
  }
  {
    unfold has_sem_type.
    asimpl.
    intros.
    unfold SN_E.
    exists (lam t1 (subst_tm (scons (var_tm 0) (funcomp (ren_tm shift) g)) e)).
    split.
    - constructor. constructor.
    - unfold SN_V.
      split.
      * reflexivity.
      * intros. asimpl.
        unfold has_sem_type in IHhas_type.
        specialize (IHhas_type (scons v' g)) as IH.
        assert (SN_G (t1 :: Gamma) (scons v' g)) as IH2. {
          apply G_Cons.
          - assumption.
          - assumption.
        }
        specialize (IH IH2).
        unfold SN_E in IH. destruct IH. exists x. destruct H2. split.
        apply H2. apply H3. 
  }
  {
    unfold has_sem_type.
    asimpl.
    intros.
    unfold has_sem_type in IHhas_type1.
    specialize (IHhas_type1 g H2).
    destruct IHhas_type1. destruct H3.
    unfold SN_E.
    inversion H4; subst.
    - unfold has_sem_type in IHhas_type2. unfold SN_E in IHhas_type2. specialize (IHhas_type2 g H2). destruct IHhas_type2.
      exists x. split.
      * destruct H5.
        specialize (SN_V_is_value t x H6) as SN_V_val.
        specialize (E_IfThenElseTrue (subst_tm g b) (subst_tm g e1) (subst_tm g e2) x H3 H5 SN_V_val) as H_true.
        assumption.
      * destruct H5. assumption.
    - unfold has_sem_type in IHhas_type3. unfold SN_E in IHhas_type3. specialize (IHhas_type3 g H2). destruct IHhas_type3.
      exists x. split.
      * destruct H5.
        specialize (SN_V_is_value t x H6) as SN_V_val.
        specialize (E_IfThenElseFalse (subst_tm g b) (subst_tm g e1) (subst_tm g e2) x H3 H5 SN_V_val) as H_false.
        assumption.
      * destruct H5. assumption. 
  }
  {
    unfold has_sem_type.
    asimpl.
    intros.
    unfold SN_E.
    unfold has_sem_type in IHhas_type1. 
    specialize (IHhas_type1 g H1) as IH1.
    specialize (IHhas_type2 g H1) as IH2.
    specialize (E_App (subst_tm g e1) (subst_tm g e2)) as H_app.
    unfold SN_E in IH1; unfold SN_E in IH2.
    destruct IH1; destruct IH2.
    destruct H2.
    destruct H3.
    destruct x; try contradiction H4.
    unfold SN_V in H4. destruct H4.
    specialize (H6 x0).
    destruct H6. apply H5.
    specialize (SN_V_is_value t1 x0 H5) as HS_v. 
    destruct H6.
    specialize (SN_V_is_value t2 x1 H7) as SN_V_val.
    specialize (H_app t x x1 x0 H2 H3 HS_v H6 SN_V_val).
    exists x1.
    split.
    - assumption.
    - assumption.
  }    
Qed.

Lemma sn_two (e : tm) (t : ty): 
  has_sem_type nil e t ->
  SN t e.
Proof.
  intros. 
  unfold has_sem_type in H. 
  unfold SN. unfold SN_E in H.
  specialize (H ids G_Empty). 
  asimpl. 
  rewrite instId'_tm in H. 
  assumption. 
Qed.





