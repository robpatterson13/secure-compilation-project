Require Import core fintype constants.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive binary : Type :=
  | bzero : binary -> binary
  | bone : binary -> binary
  | bend : binary.

Lemma congr_bzero {s0 : binary} {t0 : binary} (H0 : s0 = t0) :
  bzero s0 = bzero t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => bzero x) H0)).
Qed.

Lemma congr_bone {s0 : binary} {t0 : binary} (H0 : s0 = t0) :
  bone s0 = bone t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => bone x) H0)).
Qed.

Lemma congr_bend : bend = bend.
Proof.
exact (eq_refl).
Qed.

Inductive cond_sym : Type :=
  | leq : cond_sym
  | geq : cond_sym
  | gt : cond_sym
  | lt : cond_sym
  | nleq : cond_sym
  | ngeq : cond_sym
  | ngt : cond_sym
  | nlt : cond_sym.

Lemma congr_leq : leq = leq.
Proof.
exact (eq_refl).
Qed.

Lemma congr_geq : geq = geq.
Proof.
exact (eq_refl).
Qed.

Lemma congr_gt : gt = gt.
Proof.
exact (eq_refl).
Qed.

Lemma congr_lt : lt = lt.
Proof.
exact (eq_refl).
Qed.

Lemma congr_nleq : nleq = nleq.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ngeq : ngeq = ngeq.
Proof.
exact (eq_refl).
Qed.

Lemma congr_ngt : ngt = ngt.
Proof.
exact (eq_refl).
Qed.

Lemma congr_nlt : nlt = nlt.
Proof.
exact (eq_refl).
Qed.

Definition Lcarrier := L.(labels).

Inductive label (n_label : nat) : Type :=
  | var_label : fin n_label -> label n_label
  | latl : Lcarrier -> label n_label
  | ljoin : label n_label -> label n_label -> label n_label
  | lmeet : label n_label -> label n_label -> label n_label.

Lemma congr_latl {m_label : nat} {s0 : Lcarrier} {t0 : Lcarrier}
  (H0 : s0 = t0) : latl m_label s0 = latl m_label t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => latl m_label x) H0)).
Qed.

Lemma congr_ljoin {m_label : nat} {s0 : label m_label} {s1 : label m_label}
  {t0 : label m_label} {t1 : label m_label} (H0 : s0 = t0) (H1 : s1 = t1) :
  ljoin m_label s0 s1 = ljoin m_label t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ljoin m_label x s1) H0))
         (ap (fun x => ljoin m_label t0 x) H1)).
Qed.

Lemma congr_lmeet {m_label : nat} {s0 : label m_label} {s1 : label m_label}
  {t0 : label m_label} {t1 : label m_label} (H0 : s0 = t0) (H1 : s1 = t1) :
  lmeet m_label s0 s1 = lmeet m_label t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lmeet m_label x s1) H0))
         (ap (fun x => lmeet m_label t0 x) H1)).
Qed.

Lemma upRen_label_label {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_label_label (p : nat) {m : nat} {n : nat}
  (xi : fin m -> fin n) : fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_label {m_label : nat} {n_label : nat}
(xi_label : fin m_label -> fin n_label) (s : label m_label) {struct s} :
label n_label :=
  match s with
  | var_label _ s0 => var_label n_label (xi_label s0)
  | latl _ s0 => latl n_label s0
  | ljoin _ s0 s1 =>
      ljoin n_label (ren_label xi_label s0) (ren_label xi_label s1)
  | lmeet _ s0 s1 =>
      lmeet n_label (ren_label xi_label s0) (ren_label xi_label s1)
  end.

Lemma up_label_label {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) : fin (S m) -> label (S n_label).
Proof.
exact (scons (var_label (S n_label) var_zero)
         (funcomp (ren_label shift) sigma)).
Defined.

Lemma up_list_label_label (p : nat) {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) : fin (plus p m) -> label (plus p n_label).
Proof.
exact (scons_p p (funcomp (var_label (plus p n_label)) (zero_p p))
         (funcomp (ren_label (shift_p p)) sigma)).
Defined.

Fixpoint subst_label {m_label : nat} {n_label : nat}
(sigma_label : fin m_label -> label n_label) (s : label m_label) {struct s} :
label n_label :=
  match s with
  | var_label _ s0 => sigma_label s0
  | latl _ s0 => latl n_label s0
  | ljoin _ s0 s1 =>
      ljoin n_label (subst_label sigma_label s0) (subst_label sigma_label s1)
  | lmeet _ s0 s1 =>
      lmeet n_label (subst_label sigma_label s0) (subst_label sigma_label s1)
  end.

Lemma upId_label_label {m_label : nat} (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_label_label sigma x = var_label (S m_label) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_label shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_label_label {p : nat} {m_label : nat}
  (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_list_label_label p sigma x = var_label (plus p m_label) x.
Proof.
exact (fun n =>
       scons_p_eta (var_label (plus p m_label))
         (fun n => ap (ren_label (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_label {m_label : nat}
(sigma_label : fin m_label -> label m_label)
(Eq_label : forall x, sigma_label x = var_label m_label x)
(s : label m_label) {struct s} : subst_label sigma_label s = s :=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin (idSubst_label sigma_label Eq_label s0)
        (idSubst_label sigma_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet (idSubst_label sigma_label Eq_label s0)
        (idSubst_label sigma_label Eq_label s1)
  end.

Lemma upExtRen_label_label {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_label_label xi x = upRen_label_label zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_label_label {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_label_label p xi x = upRen_list_label_label p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_label {m_label : nat} {n_label : nat}
(xi_label : fin m_label -> fin n_label)
(zeta_label : fin m_label -> fin n_label)
(Eq_label : forall x, xi_label x = zeta_label x) (s : label m_label) {struct
 s} :
ren_label xi_label s = ren_label zeta_label s :=
  match s with
  | var_label _ s0 => ap (var_label n_label) (Eq_label s0)
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin (extRen_label xi_label zeta_label Eq_label s0)
        (extRen_label xi_label zeta_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet (extRen_label xi_label zeta_label Eq_label s0)
        (extRen_label xi_label zeta_label Eq_label s1)
  end.

Lemma upExt_label_label {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_label_label sigma x = up_label_label tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_label shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_label_label {p : nat} {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_label_label p sigma x = up_list_label_label p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_label (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_label {m_label : nat} {n_label : nat}
(sigma_label : fin m_label -> label n_label)
(tau_label : fin m_label -> label n_label)
(Eq_label : forall x, sigma_label x = tau_label x) (s : label m_label)
{struct s} : subst_label sigma_label s = subst_label tau_label s :=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin (ext_label sigma_label tau_label Eq_label s0)
        (ext_label sigma_label tau_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet (ext_label sigma_label tau_label Eq_label s0)
        (ext_label sigma_label tau_label Eq_label s1)
  end.

Lemma up_ren_ren_label_label {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_label_label zeta) (upRen_label_label xi) x =
  upRen_label_label rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_label_label {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_label_label p zeta) (upRen_list_label_label p xi) x =
  upRen_list_label_label p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_label {k_label : nat} {l_label : nat} {m_label : nat}
(xi_label : fin m_label -> fin k_label)
(zeta_label : fin k_label -> fin l_label)
(rho_label : fin m_label -> fin l_label)
(Eq_label : forall x, funcomp zeta_label xi_label x = rho_label x)
(s : label m_label) {struct s} :
ren_label zeta_label (ren_label xi_label s) = ren_label rho_label s :=
  match s with
  | var_label _ s0 => ap (var_label l_label) (Eq_label s0)
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin
        (compRenRen_label xi_label zeta_label rho_label Eq_label s0)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet
        (compRenRen_label xi_label zeta_label rho_label Eq_label s0)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s1)
  end.

Lemma up_ren_subst_label_label {k : nat} {l : nat} {m_label : nat}
  (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_label_label tau) (upRen_label_label xi) x =
  up_label_label theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_label shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_label_label {p : nat} {k : nat} {l : nat}
  {m_label : nat} (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_label_label p tau) (upRen_list_label_label p xi) x =
  up_list_label_label p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_label (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_label {k_label : nat} {l_label : nat} {m_label : nat}
(xi_label : fin m_label -> fin k_label)
(tau_label : fin k_label -> label l_label)
(theta_label : fin m_label -> label l_label)
(Eq_label : forall x, funcomp tau_label xi_label x = theta_label x)
(s : label m_label) {struct s} :
subst_label tau_label (ren_label xi_label s) = subst_label theta_label s :=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin
        (compRenSubst_label xi_label tau_label theta_label Eq_label s0)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet
        (compRenSubst_label xi_label tau_label theta_label Eq_label s0)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s1)
  end.

Lemma up_subst_ren_label_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (zeta_label : fin l_label -> fin m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_label_label zeta_label)) (up_label_label sigma) x =
  up_label_label theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_label shift (upRen_label_label zeta_label)
                (funcomp shift zeta_label) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_label zeta_label shift
                      (funcomp shift zeta_label) (fun x => eq_refl)
                      (sigma fin_n)))
                (ap (ren_label shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_label_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (zeta_label : fin l_label -> fin m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_list_label_label p zeta_label))
    (up_list_label_label p sigma) x =
  up_list_label_label p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_label (plus p m_label)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_label (shift_p p)
                  (upRen_list_label_label p zeta_label)
                  (funcomp (shift_p p) zeta_label)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_label zeta_label (shift_p p)
                        (funcomp (shift_p p) zeta_label) (fun x => eq_refl)
                        (sigma n)))
                  (ap (ren_label (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_label {k_label : nat} {l_label : nat} {m_label : nat}
(sigma_label : fin m_label -> label k_label)
(zeta_label : fin k_label -> fin l_label)
(theta_label : fin m_label -> label l_label)
(Eq_label : forall x,
            funcomp (ren_label zeta_label) sigma_label x = theta_label x)
(s : label m_label) {struct s} :
ren_label zeta_label (subst_label sigma_label s) = subst_label theta_label s
:=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s0)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s0)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s1)
  end.

Lemma up_subst_subst_label_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (tau_label : fin l_label -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_label_label tau_label)) (up_label_label sigma) x =
  up_label_label theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_label shift (up_label_label tau_label)
                (funcomp (up_label_label tau_label) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_label tau_label shift
                      (funcomp (ren_label shift) tau_label)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_label shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_label_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (tau_label : fin l_label -> label m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_list_label_label p tau_label))
    (up_list_label_label p sigma) x =
  up_list_label_label p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_label (plus p l_label)) (zero_p p)) _ _
            n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_label (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_label (shift_p p)
                  (up_list_label_label p tau_label)
                  (funcomp (up_list_label_label p tau_label) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_label tau_label (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_label (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_label {k_label : nat} {l_label : nat} {m_label : nat}
(sigma_label : fin m_label -> label k_label)
(tau_label : fin k_label -> label l_label)
(theta_label : fin m_label -> label l_label)
(Eq_label : forall x,
            funcomp (subst_label tau_label) sigma_label x = theta_label x)
(s : label m_label) {struct s} :
subst_label tau_label (subst_label sigma_label s) = subst_label theta_label s
:=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s0)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s0)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s1)
  end.

Lemma renRen_label {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (zeta_label : fin k_label -> fin l_label) (s : label m_label) :
  ren_label zeta_label (ren_label xi_label s) =
  ren_label (funcomp zeta_label xi_label) s.
Proof.
exact (compRenRen_label xi_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_label_pointwise {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (zeta_label : fin k_label -> fin l_label) :
  pointwise_relation _ eq
    (funcomp (ren_label zeta_label) (ren_label xi_label))
    (ren_label (funcomp zeta_label xi_label)).
Proof.
exact (fun s => compRenRen_label xi_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_label {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (tau_label : fin k_label -> label l_label) (s : label m_label) :
  subst_label tau_label (ren_label xi_label s) =
  subst_label (funcomp tau_label xi_label) s.
Proof.
exact (compRenSubst_label xi_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_label_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (xi_label : fin m_label -> fin k_label)
  (tau_label : fin k_label -> label l_label) :
  pointwise_relation _ eq
    (funcomp (subst_label tau_label) (ren_label xi_label))
    (subst_label (funcomp tau_label xi_label)).
Proof.
exact (fun s => compRenSubst_label xi_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma substRen_label {k_label : nat} {l_label : nat} {m_label : nat}
  (sigma_label : fin m_label -> label k_label)
  (zeta_label : fin k_label -> fin l_label) (s : label m_label) :
  ren_label zeta_label (subst_label sigma_label s) =
  subst_label (funcomp (ren_label zeta_label) sigma_label) s.
Proof.
exact (compSubstRen_label sigma_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma substRen_label_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (zeta_label : fin k_label -> fin l_label) :
  pointwise_relation _ eq
    (funcomp (ren_label zeta_label) (subst_label sigma_label))
    (subst_label (funcomp (ren_label zeta_label) sigma_label)).
Proof.
exact (fun s =>
       compSubstRen_label sigma_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_label {k_label : nat} {l_label : nat} {m_label : nat}
  (sigma_label : fin m_label -> label k_label)
  (tau_label : fin k_label -> label l_label) (s : label m_label) :
  subst_label tau_label (subst_label sigma_label s) =
  subst_label (funcomp (subst_label tau_label) sigma_label) s.
Proof.
exact (compSubstSubst_label sigma_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_label_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (tau_label : fin k_label -> label l_label) :
  pointwise_relation _ eq
    (funcomp (subst_label tau_label) (subst_label sigma_label))
    (subst_label (funcomp (subst_label tau_label) sigma_label)).
Proof.
exact (fun s =>
       compSubstSubst_label sigma_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_label_label {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label (S n_label)) (upRen_label_label xi) x =
  up_label_label sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_label shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_label_label {p : nat} {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label (plus p n_label)) (upRen_list_label_label p xi) x =
  up_list_label_label p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_label (plus p n_label)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_label (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_label {m_label : nat} {n_label : nat}
(xi_label : fin m_label -> fin n_label)
(sigma_label : fin m_label -> label n_label)
(Eq_label : forall x, funcomp (var_label n_label) xi_label x = sigma_label x)
(s : label m_label) {struct s} :
ren_label xi_label s = subst_label sigma_label s :=
  match s with
  | var_label _ s0 => Eq_label s0
  | latl _ s0 => congr_latl (eq_refl s0)
  | ljoin _ s0 s1 =>
      congr_ljoin (rinst_inst_label xi_label sigma_label Eq_label s0)
        (rinst_inst_label xi_label sigma_label Eq_label s1)
  | lmeet _ s0 s1 =>
      congr_lmeet (rinst_inst_label xi_label sigma_label Eq_label s0)
        (rinst_inst_label xi_label sigma_label Eq_label s1)
  end.

Lemma rinstInst'_label {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) (s : label m_label) :
  ren_label xi_label s = subst_label (funcomp (var_label n_label) xi_label) s.
Proof.
exact (rinst_inst_label xi_label _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_label_pointwise {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) :
  pointwise_relation _ eq (ren_label xi_label)
    (subst_label (funcomp (var_label n_label) xi_label)).
Proof.
exact (fun s => rinst_inst_label xi_label _ (fun n => eq_refl) s).
Qed.

Lemma instId'_label {m_label : nat} (s : label m_label) :
  subst_label (var_label m_label) s = s.
Proof.
exact (idSubst_label (var_label m_label) (fun n => eq_refl) s).
Qed.

Lemma instId'_label_pointwise {m_label : nat} :
  pointwise_relation _ eq (subst_label (var_label m_label)) id.
Proof.
exact (fun s => idSubst_label (var_label m_label) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_label {m_label : nat} (s : label m_label) : ren_label id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_label s) (rinstInst'_label id s)).
Qed.

Lemma rinstId'_label_pointwise {m_label : nat} :
  pointwise_relation _ eq (@ren_label m_label m_label id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_label s) (rinstInst'_label id s)).
Qed.

Lemma varL'_label {m_label : nat} {n_label : nat}
  (sigma_label : fin m_label -> label n_label) (x : fin m_label) :
  subst_label sigma_label (var_label m_label x) = sigma_label x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_label_pointwise {m_label : nat} {n_label : nat}
  (sigma_label : fin m_label -> label n_label) :
  pointwise_relation _ eq
    (funcomp (subst_label sigma_label) (var_label m_label)) sigma_label.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_label {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) (x : fin m_label) :
  ren_label xi_label (var_label m_label x) = var_label n_label (xi_label x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_label_pointwise {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) :
  pointwise_relation _ eq (funcomp (ren_label xi_label) (var_label m_label))
    (funcomp (var_label n_label) xi_label).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive constr (n_label : nat) : Type :=
    condition : cond_sym -> label n_label -> label n_label -> constr n_label.

Lemma congr_condition {m_label : nat} {s0 : cond_sym} {s1 : label m_label}
  {s2 : label m_label} {t0 : cond_sym} {t1 : label m_label}
  {t2 : label m_label} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  condition m_label s0 s1 s2 = condition m_label t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => condition m_label x s1 s2) H0))
            (ap (fun x => condition m_label t0 x s2) H1))
         (ap (fun x => condition m_label t0 t1 x) H2)).
Qed.

Definition ren_constr {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | condition _ s0 s1 s2 =>
      condition n_label s0 (ren_label xi_label s1) (ren_label xi_label s2)
  end.

Definition subst_constr {m_label : nat} {n_label : nat}
  (sigma_label : fin m_label -> label n_label) (s : constr m_label) :
  constr n_label :=
  match s with
  | condition _ s0 s1 s2 =>
      condition n_label s0 (subst_label sigma_label s1)
        (subst_label sigma_label s2)
  end.

Definition idSubst_constr {m_label : nat}
  (sigma_label : fin m_label -> label m_label)
  (Eq_label : forall x, sigma_label x = var_label m_label x)
  (s : constr m_label) : subst_constr sigma_label s = s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0) (idSubst_label sigma_label Eq_label s1)
        (idSubst_label sigma_label Eq_label s2)
  end.

Definition extRen_constr {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label)
  (zeta_label : fin m_label -> fin n_label)
  (Eq_label : forall x, xi_label x = zeta_label x) (s : constr m_label) :
  ren_constr xi_label s = ren_constr zeta_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (extRen_label xi_label zeta_label Eq_label s1)
        (extRen_label xi_label zeta_label Eq_label s2)
  end.

Definition ext_constr {m_label : nat} {n_label : nat}
  (sigma_label : fin m_label -> label n_label)
  (tau_label : fin m_label -> label n_label)
  (Eq_label : forall x, sigma_label x = tau_label x) (s : constr m_label) :
  subst_constr sigma_label s = subst_constr tau_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (ext_label sigma_label tau_label Eq_label s1)
        (ext_label sigma_label tau_label Eq_label s2)
  end.

Definition compRenRen_constr {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (zeta_label : fin k_label -> fin l_label)
  (rho_label : fin m_label -> fin l_label)
  (Eq_label : forall x, funcomp zeta_label xi_label x = rho_label x)
  (s : constr m_label) :
  ren_constr zeta_label (ren_constr xi_label s) = ren_constr rho_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s1)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s2)
  end.

Definition compRenSubst_constr {k_label : nat} {l_label : nat}
  {m_label : nat} (xi_label : fin m_label -> fin k_label)
  (tau_label : fin k_label -> label l_label)
  (theta_label : fin m_label -> label l_label)
  (Eq_label : forall x, funcomp tau_label xi_label x = theta_label x)
  (s : constr m_label) :
  subst_constr tau_label (ren_constr xi_label s) = subst_constr theta_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s1)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s2)
  end.

Definition compSubstRen_constr {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (zeta_label : fin k_label -> fin l_label)
  (theta_label : fin m_label -> label l_label)
  (Eq_label : forall x,
              funcomp (ren_label zeta_label) sigma_label x = theta_label x)
  (s : constr m_label) :
  ren_constr zeta_label (subst_constr sigma_label s) =
  subst_constr theta_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s1)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s2)
  end.

Definition compSubstSubst_constr {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (tau_label : fin k_label -> label l_label)
  (theta_label : fin m_label -> label l_label)
  (Eq_label : forall x,
              funcomp (subst_label tau_label) sigma_label x = theta_label x)
  (s : constr m_label) :
  subst_constr tau_label (subst_constr sigma_label s) =
  subst_constr theta_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s1)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s2)
  end.

Lemma renRen_constr {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (zeta_label : fin k_label -> fin l_label) (s : constr m_label) :
  ren_constr zeta_label (ren_constr xi_label s) =
  ren_constr (funcomp zeta_label xi_label) s.
Proof.
exact (compRenRen_constr xi_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_constr_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (xi_label : fin m_label -> fin k_label)
  (zeta_label : fin k_label -> fin l_label) :
  pointwise_relation _ eq
    (funcomp (ren_constr zeta_label) (ren_constr xi_label))
    (ren_constr (funcomp zeta_label xi_label)).
Proof.
exact (fun s => compRenRen_constr xi_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_constr {k_label : nat} {l_label : nat} {m_label : nat}
  (xi_label : fin m_label -> fin k_label)
  (tau_label : fin k_label -> label l_label) (s : constr m_label) :
  subst_constr tau_label (ren_constr xi_label s) =
  subst_constr (funcomp tau_label xi_label) s.
Proof.
exact (compRenSubst_constr xi_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_constr_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (xi_label : fin m_label -> fin k_label)
  (tau_label : fin k_label -> label l_label) :
  pointwise_relation _ eq
    (funcomp (subst_constr tau_label) (ren_constr xi_label))
    (subst_constr (funcomp tau_label xi_label)).
Proof.
exact (fun s => compRenSubst_constr xi_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma substRen_constr {k_label : nat} {l_label : nat} {m_label : nat}
  (sigma_label : fin m_label -> label k_label)
  (zeta_label : fin k_label -> fin l_label) (s : constr m_label) :
  ren_constr zeta_label (subst_constr sigma_label s) =
  subst_constr (funcomp (ren_label zeta_label) sigma_label) s.
Proof.
exact (compSubstRen_constr sigma_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma substRen_constr_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (zeta_label : fin k_label -> fin l_label) :
  pointwise_relation _ eq
    (funcomp (ren_constr zeta_label) (subst_constr sigma_label))
    (subst_constr (funcomp (ren_label zeta_label) sigma_label)).
Proof.
exact (fun s =>
       compSubstRen_constr sigma_label zeta_label _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_constr {k_label : nat} {l_label : nat} {m_label : nat}
  (sigma_label : fin m_label -> label k_label)
  (tau_label : fin k_label -> label l_label) (s : constr m_label) :
  subst_constr tau_label (subst_constr sigma_label s) =
  subst_constr (funcomp (subst_label tau_label) sigma_label) s.
Proof.
exact (compSubstSubst_constr sigma_label tau_label _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_constr_pointwise {k_label : nat} {l_label : nat}
  {m_label : nat} (sigma_label : fin m_label -> label k_label)
  (tau_label : fin k_label -> label l_label) :
  pointwise_relation _ eq
    (funcomp (subst_constr tau_label) (subst_constr sigma_label))
    (subst_constr (funcomp (subst_label tau_label) sigma_label)).
Proof.
exact (fun s =>
       compSubstSubst_constr sigma_label tau_label _ (fun n => eq_refl) s).
Qed.

Definition rinst_inst_constr {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label)
  (sigma_label : fin m_label -> label n_label)
  (Eq_label : forall x,
              funcomp (var_label n_label) xi_label x = sigma_label x)
  (s : constr m_label) :
  ren_constr xi_label s = subst_constr sigma_label s :=
  match s with
  | condition _ s0 s1 s2 =>
      congr_condition (eq_refl s0)
        (rinst_inst_label xi_label sigma_label Eq_label s1)
        (rinst_inst_label xi_label sigma_label Eq_label s2)
  end.

Lemma rinstInst'_constr {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) (s : constr m_label) :
  ren_constr xi_label s =
  subst_constr (funcomp (var_label n_label) xi_label) s.
Proof.
exact (rinst_inst_constr xi_label _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_constr_pointwise {m_label : nat} {n_label : nat}
  (xi_label : fin m_label -> fin n_label) :
  pointwise_relation _ eq (ren_constr xi_label)
    (subst_constr (funcomp (var_label n_label) xi_label)).
Proof.
exact (fun s => rinst_inst_constr xi_label _ (fun n => eq_refl) s).
Qed.

Lemma instId'_constr {m_label : nat} (s : constr m_label) :
  subst_constr (var_label m_label) s = s.
Proof.
exact (idSubst_constr (var_label m_label) (fun n => eq_refl) s).
Qed.

Lemma instId'_constr_pointwise {m_label : nat} :
  pointwise_relation _ eq (subst_constr (var_label m_label)) id.
Proof.
exact (fun s => idSubst_constr (var_label m_label) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_constr {m_label : nat} (s : constr m_label) :
  ren_constr id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_constr s) (rinstInst'_constr id s)).
Qed.

Lemma rinstId'_constr_pointwise {m_label : nat} :
  pointwise_relation _ eq (@ren_constr m_label m_label id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_constr s) (rinstInst'_constr id s)).
Qed.

Definition op := list binary -> Dist binary.

Inductive tm (n_label n_tm : nat) : Type :=
  | var_tm : fin n_tm -> tm n_label n_tm
  | error : tm n_label n_tm
  | skip : tm n_label n_tm
  | bitstring : binary -> tm n_label n_tm
  | loc : nat -> tm n_label n_tm
  | fixlam : tm n_label (S (S n_tm)) -> tm n_label n_tm
  | tlam : tm n_label n_tm -> tm n_label n_tm
  | l_lam : tm (S n_label) n_tm -> tm n_label n_tm
  | Op : op -> list (tm n_label n_tm) -> tm n_label n_tm
  | zero : tm n_label n_tm -> tm n_label n_tm
  | app : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
  | alloc : tm n_label n_tm -> tm n_label n_tm
  | dealloc : tm n_label n_tm -> tm n_label n_tm
  | assign : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
  | tm_pair : tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
  | left_tm : tm n_label n_tm -> tm n_label n_tm
  | right_tm : tm n_label n_tm -> tm n_label n_tm
  | inl : tm n_label n_tm -> tm n_label n_tm
  | inr : tm n_label n_tm -> tm n_label n_tm
  | case :
      tm n_label n_tm ->
      tm n_label (S n_tm) -> tm n_label (S n_tm) -> tm n_label n_tm
  | tapp : tm n_label n_tm -> tm n_label n_tm
  | lapp : tm n_label n_tm -> label n_label -> tm n_label n_tm
  | pack : tm n_label n_tm -> tm n_label n_tm
  | unpack : tm n_label n_tm -> tm n_label (S n_tm) -> tm n_label n_tm
  | if_tm :
      tm n_label n_tm ->
      tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
  | if_c :
      constr n_label -> tm n_label n_tm -> tm n_label n_tm -> tm n_label n_tm
  | sync : tm n_label n_tm -> tm n_label n_tm.

Lemma congr_error {m_label m_tm : nat} :
  error m_label m_tm = error m_label m_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_skip {m_label m_tm : nat} : skip m_label m_tm = skip m_label m_tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_bitstring {m_label m_tm : nat} {s0 : binary} {t0 : binary}
  (H0 : s0 = t0) : bitstring m_label m_tm s0 = bitstring m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => bitstring m_label m_tm x) H0)).
Qed.

Lemma congr_loc {m_label m_tm : nat} {s0 : nat} {t0 : nat} (H0 : s0 = t0) :
  loc m_label m_tm s0 = loc m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => loc m_label m_tm x) H0)).
Qed.

Lemma congr_fixlam {m_label m_tm : nat} {s0 : tm m_label (S (S m_tm))}
  {t0 : tm m_label (S (S m_tm))} (H0 : s0 = t0) :
  fixlam m_label m_tm s0 = fixlam m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => fixlam m_label m_tm x) H0)).
Qed.

Lemma congr_tlam {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  tlam m_label m_tm s0 = tlam m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tlam m_label m_tm x) H0)).
Qed.

Lemma congr_l_lam {m_label m_tm : nat} {s0 : tm (S m_label) m_tm}
  {t0 : tm (S m_label) m_tm} (H0 : s0 = t0) :
  l_lam m_label m_tm s0 = l_lam m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => l_lam m_label m_tm x) H0)).
Qed.

Lemma congr_Op {m_label m_tm : nat} {s0 : op} {s1 : list (tm m_label m_tm)}
  {t0 : op} {t1 : list (tm m_label m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  Op m_label m_tm s0 s1 = Op m_label m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => Op m_label m_tm x s1) H0))
         (ap (fun x => Op m_label m_tm t0 x) H1)).
Qed.

Lemma congr_zero {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  zero m_label m_tm s0 = zero m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => zero m_label m_tm x) H0)).
Qed.

Lemma congr_app {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label m_tm} {t0 : tm m_label m_tm} {t1 : tm m_label m_tm}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  app m_label m_tm s0 s1 = app m_label m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app m_label m_tm x s1) H0))
         (ap (fun x => app m_label m_tm t0 x) H1)).
Qed.

Lemma congr_alloc {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  alloc m_label m_tm s0 = alloc m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => alloc m_label m_tm x) H0)).
Qed.

Lemma congr_dealloc {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  dealloc m_label m_tm s0 = dealloc m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => dealloc m_label m_tm x) H0)).
Qed.

Lemma congr_assign {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label m_tm} {t0 : tm m_label m_tm} {t1 : tm m_label m_tm}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  assign m_label m_tm s0 s1 = assign m_label m_tm t0 t1.
Proof.
exact (eq_trans
         (eq_trans eq_refl (ap (fun x => assign m_label m_tm x s1) H0))
         (ap (fun x => assign m_label m_tm t0 x) H1)).
Qed.

Lemma congr_tm_pair {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label m_tm} {t0 : tm m_label m_tm} {t1 : tm m_label m_tm}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  tm_pair m_label m_tm s0 s1 = tm_pair m_label m_tm t0 t1.
Proof.
exact (eq_trans
         (eq_trans eq_refl (ap (fun x => tm_pair m_label m_tm x s1) H0))
         (ap (fun x => tm_pair m_label m_tm t0 x) H1)).
Qed.

Lemma congr_left_tm {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  left_tm m_label m_tm s0 = left_tm m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => left_tm m_label m_tm x) H0)).
Qed.

Lemma congr_right_tm {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  right_tm m_label m_tm s0 = right_tm m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => right_tm m_label m_tm x) H0)).
Qed.

Lemma congr_inl {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  inl m_label m_tm s0 = inl m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => inl m_label m_tm x) H0)).
Qed.

Lemma congr_inr {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  inr m_label m_tm s0 = inr m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => inr m_label m_tm x) H0)).
Qed.

Lemma congr_case {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label (S m_tm)} {s2 : tm m_label (S m_tm)}
  {t0 : tm m_label m_tm} {t1 : tm m_label (S m_tm)}
  {t2 : tm m_label (S m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  case m_label m_tm s0 s1 s2 = case m_label m_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => case m_label m_tm x s1 s2) H0))
            (ap (fun x => case m_label m_tm t0 x s2) H1))
         (ap (fun x => case m_label m_tm t0 t1 x) H2)).
Qed.

Lemma congr_tapp {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  tapp m_label m_tm s0 = tapp m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => tapp m_label m_tm x) H0)).
Qed.

Lemma congr_lapp {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : label m_label} {t0 : tm m_label m_tm} {t1 : label m_label}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  lapp m_label m_tm s0 s1 = lapp m_label m_tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => lapp m_label m_tm x s1) H0))
         (ap (fun x => lapp m_label m_tm t0 x) H1)).
Qed.

Lemma congr_pack {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  pack m_label m_tm s0 = pack m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pack m_label m_tm x) H0)).
Qed.

Lemma congr_unpack {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label (S m_tm)} {t0 : tm m_label m_tm}
  {t1 : tm m_label (S m_tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  unpack m_label m_tm s0 s1 = unpack m_label m_tm t0 t1.
Proof.
exact (eq_trans
         (eq_trans eq_refl (ap (fun x => unpack m_label m_tm x s1) H0))
         (ap (fun x => unpack m_label m_tm t0 x) H1)).
Qed.

Lemma congr_if_tm {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {s1 : tm m_label m_tm} {s2 : tm m_label m_tm} {t0 : tm m_label m_tm}
  {t1 : tm m_label m_tm} {t2 : tm m_label m_tm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) : if_tm m_label m_tm s0 s1 s2 = if_tm m_label m_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => if_tm m_label m_tm x s1 s2) H0))
            (ap (fun x => if_tm m_label m_tm t0 x s2) H1))
         (ap (fun x => if_tm m_label m_tm t0 t1 x) H2)).
Qed.

Lemma congr_if_c {m_label m_tm : nat} {s0 : constr m_label}
  {s1 : tm m_label m_tm} {s2 : tm m_label m_tm} {t0 : constr m_label}
  {t1 : tm m_label m_tm} {t2 : tm m_label m_tm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) : if_c m_label m_tm s0 s1 s2 = if_c m_label m_tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => if_c m_label m_tm x s1 s2) H0))
            (ap (fun x => if_c m_label m_tm t0 x s2) H1))
         (ap (fun x => if_c m_label m_tm t0 t1 x) H2)).
Qed.

Lemma congr_sync {m_label m_tm : nat} {s0 : tm m_label m_tm}
  {t0 : tm m_label m_tm} (H0 : s0 = t0) :
  sync m_label m_tm s0 = sync m_label m_tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => sync m_label m_tm x) H0)).
Qed.

Lemma upRen_label_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_tm_label {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_label_tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_tm_label (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_tm_tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_tm {m_label m_tm : nat} {n_label n_tm : nat}
(xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm)
(s : tm m_label m_tm) {struct s} : tm n_label n_tm :=
  match s with
  | var_tm _ _ s0 => var_tm n_label n_tm (xi_tm s0)
  | error _ _ => error n_label n_tm
  | skip _ _ => skip n_label n_tm
  | bitstring _ _ s0 => bitstring n_label n_tm s0
  | loc _ _ s0 => loc n_label n_tm s0
  | fixlam _ _ s0 =>
      fixlam n_label n_tm
        (ren_tm (upRen_tm_label (upRen_tm_label xi_label))
           (upRen_tm_tm (upRen_tm_tm xi_tm)) s0)
  | tlam _ _ s0 => tlam n_label n_tm (ren_tm xi_label xi_tm s0)
  | l_lam _ _ s0 =>
      l_lam n_label n_tm
        (ren_tm (upRen_label_label xi_label) (upRen_label_tm xi_tm) s0)
  | Op _ _ s0 s1 => Op n_label n_tm s0 (list_map (ren_tm xi_label xi_tm) s1)
  | zero _ _ s0 => zero n_label n_tm (ren_tm xi_label xi_tm s0)
  | app _ _ s0 s1 =>
      app n_label n_tm (ren_tm xi_label xi_tm s0) (ren_tm xi_label xi_tm s1)
  | alloc _ _ s0 => alloc n_label n_tm (ren_tm xi_label xi_tm s0)
  | dealloc _ _ s0 => dealloc n_label n_tm (ren_tm xi_label xi_tm s0)
  | assign _ _ s0 s1 =>
      assign n_label n_tm (ren_tm xi_label xi_tm s0)
        (ren_tm xi_label xi_tm s1)
  | tm_pair _ _ s0 s1 =>
      tm_pair n_label n_tm (ren_tm xi_label xi_tm s0)
        (ren_tm xi_label xi_tm s1)
  | left_tm _ _ s0 => left_tm n_label n_tm (ren_tm xi_label xi_tm s0)
  | right_tm _ _ s0 => right_tm n_label n_tm (ren_tm xi_label xi_tm s0)
  | inl _ _ s0 => inl n_label n_tm (ren_tm xi_label xi_tm s0)
  | inr _ _ s0 => inr n_label n_tm (ren_tm xi_label xi_tm s0)
  | case _ _ s0 s1 s2 =>
      case n_label n_tm (ren_tm xi_label xi_tm s0)
        (ren_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm) s1)
        (ren_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm) s2)
  | tapp _ _ s0 => tapp n_label n_tm (ren_tm xi_label xi_tm s0)
  | lapp _ _ s0 s1 =>
      lapp n_label n_tm (ren_tm xi_label xi_tm s0) (ren_label xi_label s1)
  | pack _ _ s0 => pack n_label n_tm (ren_tm xi_label xi_tm s0)
  | unpack _ _ s0 s1 =>
      unpack n_label n_tm (ren_tm xi_label xi_tm s0)
        (ren_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      if_tm n_label n_tm (ren_tm xi_label xi_tm s0)
        (ren_tm xi_label xi_tm s1) (ren_tm xi_label xi_tm s2)
  | if_c _ _ s0 s1 s2 =>
      if_c n_label n_tm (ren_constr xi_label s0) (ren_tm xi_label xi_tm s1)
        (ren_tm xi_label xi_tm s2)
  | sync _ _ s0 => sync n_label n_tm (ren_tm xi_label xi_tm s0)
  end.

Lemma up_label_tm {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) : fin m -> tm (S n_label) n_tm.
Proof.
exact (funcomp (ren_tm shift id) sigma).
Defined.

Lemma up_tm_label {m : nat} {n_label : nat} (sigma : fin m -> label n_label)
  : fin m -> label n_label.
Proof.
exact (funcomp (ren_label id) sigma).
Defined.

Lemma up_tm_tm {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) : fin (S m) -> tm n_label (S n_tm).
Proof.
exact (scons (var_tm n_label (S n_tm) var_zero)
         (funcomp (ren_tm id shift) sigma)).
Defined.

Lemma up_list_label_tm (p : nat) {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) : fin m -> tm (plus p n_label) n_tm.
Proof.
exact (funcomp (ren_tm (shift_p p) id) sigma).
Defined.

Lemma up_list_tm_label (p : nat) {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) : fin m -> label n_label.
Proof.
exact (funcomp (ren_label id) sigma).
Defined.

Lemma up_list_tm_tm (p : nat) {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) :
  fin (plus p m) -> tm n_label (plus p n_tm).
Proof.
exact (scons_p p (funcomp (var_tm n_label (plus p n_tm)) (zero_p p))
         (funcomp (ren_tm id (shift_p p)) sigma)).
Defined.

Fixpoint subst_tm {m_label m_tm : nat} {n_label n_tm : nat}
(sigma_label : fin m_label -> label n_label)
(sigma_tm : fin m_tm -> tm n_label n_tm) (s : tm m_label m_tm) {struct s} :
tm n_label n_tm :=
  match s with
  | var_tm _ _ s0 => sigma_tm s0
  | error _ _ => error n_label n_tm
  | skip _ _ => skip n_label n_tm
  | bitstring _ _ s0 => bitstring n_label n_tm s0
  | loc _ _ s0 => loc n_label n_tm s0
  | fixlam _ _ s0 =>
      fixlam n_label n_tm
        (subst_tm (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm)) s0)
  | tlam _ _ s0 => tlam n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | l_lam _ _ s0 =>
      l_lam n_label n_tm
        (subst_tm (up_label_label sigma_label) (up_label_tm sigma_tm) s0)
  | Op _ _ s0 s1 =>
      Op n_label n_tm s0 (list_map (subst_tm sigma_label sigma_tm) s1)
  | zero _ _ s0 => zero n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | app _ _ s0 s1 =>
      app n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm sigma_label sigma_tm s1)
  | alloc _ _ s0 => alloc n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | dealloc _ _ s0 => dealloc n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | assign _ _ s0 s1 =>
      assign n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm sigma_label sigma_tm s1)
  | tm_pair _ _ s0 s1 =>
      tm_pair n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm sigma_label sigma_tm s1)
  | left_tm _ _ s0 => left_tm n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | right_tm _ _ s0 =>
      right_tm n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | inl _ _ s0 => inl n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | inr _ _ s0 => inr n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | case _ _ s0 s1 s2 =>
      case n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm) s1)
        (subst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm) s2)
  | tapp _ _ s0 => tapp n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | lapp _ _ s0 s1 =>
      lapp n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_label sigma_label s1)
  | pack _ _ s0 => pack n_label n_tm (subst_tm sigma_label sigma_tm s0)
  | unpack _ _ s0 s1 =>
      unpack n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      if_tm n_label n_tm (subst_tm sigma_label sigma_tm s0)
        (subst_tm sigma_label sigma_tm s1) (subst_tm sigma_label sigma_tm s2)
  | if_c _ _ s0 s1 s2 =>
      if_c n_label n_tm (subst_constr sigma_label s0)
        (subst_tm sigma_label sigma_tm s1) (subst_tm sigma_label sigma_tm s2)
  | sync _ _ s0 => sync n_label n_tm (subst_tm sigma_label sigma_tm s0)
  end.

Lemma upId_label_tm {m_label m_tm : nat}
  (sigma : fin m_tm -> tm m_label m_tm)
  (Eq : forall x, sigma x = var_tm m_label m_tm x) :
  forall x, up_label_tm sigma x = var_tm (S m_label) m_tm x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma upId_tm_label {m_label : nat} (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_tm_label sigma x = var_label m_label x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upId_tm_tm {m_label m_tm : nat} (sigma : fin m_tm -> tm m_label m_tm)
  (Eq : forall x, sigma x = var_tm m_label m_tm x) :
  forall x, up_tm_tm sigma x = var_tm m_label (S m_tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_label_tm {p : nat} {m_label m_tm : nat}
  (sigma : fin m_tm -> tm m_label m_tm)
  (Eq : forall x, sigma x = var_tm m_label m_tm x) :
  forall x, up_list_label_tm p sigma x = var_tm (plus p m_label) m_tm x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma upId_list_tm_label {p : nat} {m_label : nat}
  (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_list_tm_label p sigma x = var_label m_label x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upId_list_tm_tm {p : nat} {m_label m_tm : nat}
  (sigma : fin m_tm -> tm m_label m_tm)
  (Eq : forall x, sigma x = var_tm m_label m_tm x) :
  forall x, up_list_tm_tm p sigma x = var_tm m_label (plus p m_tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var_tm m_label (plus p m_tm))
         (fun n => ap (ren_tm id (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_tm {m_label m_tm : nat}
(sigma_label : fin m_label -> label m_label)
(sigma_tm : fin m_tm -> tm m_label m_tm)
(Eq_label : forall x, sigma_label x = var_label m_label x)
(Eq_tm : forall x, sigma_tm x = var_tm m_label m_tm x) (s : tm m_label m_tm)
{struct s} : subst_tm sigma_label sigma_tm s = s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (idSubst_tm (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm))
           (upId_tm_label _ (upId_tm_label _ Eq_label))
           (upId_tm_tm _ (upId_tm_tm _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (idSubst_tm (up_label_label sigma_label) (up_label_tm sigma_tm)
           (upId_label_label _ Eq_label) (upId_label_tm _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_id (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm) s1)
  | zero _ _ s0 =>
      congr_zero (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upId_tm_label _ Eq_label) (upId_tm_tm _ Eq_tm) s1)
        (idSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upId_tm_label _ Eq_label) (upId_tm_tm _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_label sigma_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upId_tm_label _ Eq_label) (upId_tm_tm _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s1)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c (idSubst_constr sigma_label Eq_label s0)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s1)
        (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync (idSubst_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  end.

Lemma upExtRen_label_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_label_tm xi x = upRen_label_tm zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_tm_label {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_label xi x = upRen_tm_label zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_tm_tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_tm_tm xi x = upRen_tm_tm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_label_tm {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_label_tm p xi x = upRen_list_label_tm p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_tm_label {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_label p xi x = upRen_list_tm_label p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_tm_tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_tm_tm p xi x = upRen_list_tm_tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_tm {m_label m_tm : nat} {n_label n_tm : nat}
(xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm)
(zeta_label : fin m_label -> fin n_label) (zeta_tm : fin m_tm -> fin n_tm)
(Eq_label : forall x, xi_label x = zeta_label x)
(Eq_tm : forall x, xi_tm x = zeta_tm x) (s : tm m_label m_tm) {struct s} :
ren_tm xi_label xi_tm s = ren_tm zeta_label zeta_tm s :=
  match s with
  | var_tm _ _ s0 => ap (var_tm n_label n_tm) (Eq_tm s0)
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (extRen_tm (upRen_tm_label (upRen_tm_label xi_label))
           (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_label (upRen_tm_label zeta_label))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upExtRen_tm_label _ _ (upExtRen_tm_label _ _ Eq_label))
           (upExtRen_tm_tm _ _ (upExtRen_tm_tm _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (extRen_tm (upRen_label_label xi_label) (upRen_label_tm xi_tm)
           (upRen_label_label zeta_label) (upRen_label_tm zeta_tm)
           (upExtRen_label_label _ _ Eq_label) (upExtRen_label_tm _ _ Eq_tm)
           s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_ext
           (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm) s1)
  | zero _ _ s0 =>
      congr_zero
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_label _ _ Eq_label) (upExtRen_tm_tm _ _ Eq_tm) s1)
        (extRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_label _ _ Eq_label) (upExtRen_tm_tm _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_label xi_label zeta_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upExtRen_tm_label _ _ Eq_label) (upExtRen_tm_tm _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s1)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c (extRen_constr xi_label zeta_label Eq_label s0)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s1)
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (extRen_tm xi_label xi_tm zeta_label zeta_tm Eq_label Eq_tm s0)
  end.

Lemma upExt_label_tm {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) (tau : fin m -> tm n_label n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_label_tm sigma x = up_label_tm tau x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma upExt_tm_label {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_label sigma x = up_tm_label tau x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upExt_tm_tm {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) (tau : fin m -> tm n_label n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_tm_tm sigma x = up_tm_tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_label_tm {p : nat} {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) (tau : fin m -> tm n_label n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_label_tm p sigma x = up_list_label_tm p tau x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma upExt_list_tm_label {p : nat} {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_label p sigma x = up_list_tm_label p tau x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upExt_list_tm_tm {p : nat} {m : nat} {n_label n_tm : nat}
  (sigma : fin m -> tm n_label n_tm) (tau : fin m -> tm n_label n_tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_tm_tm p sigma x = up_list_tm_tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_tm id (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_tm {m_label m_tm : nat} {n_label n_tm : nat}
(sigma_label : fin m_label -> label n_label)
(sigma_tm : fin m_tm -> tm n_label n_tm)
(tau_label : fin m_label -> label n_label)
(tau_tm : fin m_tm -> tm n_label n_tm)
(Eq_label : forall x, sigma_label x = tau_label x)
(Eq_tm : forall x, sigma_tm x = tau_tm x) (s : tm m_label m_tm) {struct s} :
subst_tm sigma_label sigma_tm s = subst_tm tau_label tau_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (ext_tm (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_label (up_tm_label tau_label)) (up_tm_tm (up_tm_tm tau_tm))
           (upExt_tm_label _ _ (upExt_tm_label _ _ Eq_label))
           (upExt_tm_tm _ _ (upExt_tm_tm _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (ext_tm (up_label_label sigma_label) (up_label_tm sigma_tm)
           (up_label_label tau_label) (up_label_tm tau_tm)
           (upExt_label_label _ _ Eq_label) (upExt_label_tm _ _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_ext
           (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm) s1)
  | zero _ _ s0 =>
      congr_zero
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (upExt_tm_label _ _ Eq_label) (upExt_tm_tm _ _ Eq_tm) s1)
        (ext_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (upExt_tm_label _ _ Eq_label) (upExt_tm_tm _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_label sigma_label tau_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (upExt_tm_label _ _ Eq_label) (upExt_tm_tm _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s1)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c (ext_constr sigma_label tau_label Eq_label s0)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s1)
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (ext_tm sigma_label sigma_tm tau_label tau_tm Eq_label Eq_tm s0)
  end.

Lemma up_ren_ren_label_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_label_tm zeta) (upRen_label_tm xi) x = upRen_label_tm rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_tm_label {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_tm_label zeta) (upRen_tm_label xi) x = upRen_tm_label rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_tm_tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_tm_tm zeta) (upRen_tm_tm xi) x = upRen_tm_tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_label_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_label_tm p zeta) (upRen_list_label_tm p xi) x =
  upRen_list_label_tm p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_tm_label {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_label p zeta) (upRen_list_tm_label p xi) x =
  upRen_list_tm_label p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_tm_tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_tm_tm p zeta) (upRen_list_tm_tm p xi) x =
  upRen_list_tm_tm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_tm {k_label k_tm : nat} {l_label l_tm : nat}
{m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
(xi_tm : fin m_tm -> fin k_tm) (zeta_label : fin k_label -> fin l_label)
(zeta_tm : fin k_tm -> fin l_tm) (rho_label : fin m_label -> fin l_label)
(rho_tm : fin m_tm -> fin l_tm)
(Eq_label : forall x, funcomp zeta_label xi_label x = rho_label x)
(Eq_tm : forall x, funcomp zeta_tm xi_tm x = rho_tm x) (s : tm m_label m_tm)
{struct s} :
ren_tm zeta_label zeta_tm (ren_tm xi_label xi_tm s) =
ren_tm rho_label rho_tm s :=
  match s with
  | var_tm _ _ s0 => ap (var_tm l_label l_tm) (Eq_tm s0)
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (compRenRen_tm (upRen_tm_label (upRen_tm_label xi_label))
           (upRen_tm_tm (upRen_tm_tm xi_tm))
           (upRen_tm_label (upRen_tm_label zeta_label))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (upRen_tm_label (upRen_tm_label rho_label))
           (upRen_tm_tm (upRen_tm_tm rho_tm)) Eq_label
           (up_ren_ren _ _ _ (up_ren_ren _ _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (compRenRen_tm (upRen_label_label xi_label) (upRen_label_tm xi_tm)
           (upRen_label_label zeta_label) (upRen_label_tm zeta_tm)
           (upRen_label_label rho_label) (upRen_label_tm rho_tm)
           (up_ren_ren _ _ _ Eq_label) Eq_tm s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_comp
           (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
              Eq_label Eq_tm)
           s1)
  | zero _ _ s0 =>
      congr_zero
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upRen_tm_label rho_label) (upRen_tm_tm rho_tm) Eq_label
           (up_ren_ren _ _ _ Eq_tm) s1)
        (compRenRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upRen_tm_label rho_label) (upRen_tm_tm rho_tm) Eq_label
           (up_ren_ren _ _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (upRen_tm_label rho_label) (upRen_tm_tm rho_tm) Eq_label
           (up_ren_ren _ _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s1)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c
        (compRenRen_constr xi_label zeta_label rho_label Eq_label s0)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s1)
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (compRenRen_tm xi_label xi_tm zeta_label zeta_tm rho_label rho_tm
           Eq_label Eq_tm s0)
  end.

Lemma up_ren_subst_label_tm {k : nat} {l : nat} {m_label m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_label m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_label_tm tau) (upRen_label_tm xi) x = up_label_tm theta x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma up_ren_subst_tm_label {k : nat} {l : nat} {m_label : nat}
  (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_tm_label tau) (upRen_tm_label xi) x = up_tm_label theta x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma up_ren_subst_tm_tm {k : nat} {l : nat} {m_label m_tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> tm m_label m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_tm_tm tau) (upRen_tm_tm xi) x = up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_label_tm {p : nat} {k : nat} {l : nat}
  {m_label m_tm : nat} (xi : fin k -> fin l) (tau : fin l -> tm m_label m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_label_tm p tau) (upRen_list_label_tm p xi) x =
  up_list_label_tm p theta x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma up_ren_subst_list_tm_label {p : nat} {k : nat} {l : nat}
  {m_label : nat} (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_label p tau) (upRen_list_tm_label p xi) x =
  up_list_tm_label p theta x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma up_ren_subst_list_tm_tm {p : nat} {k : nat} {l : nat}
  {m_label m_tm : nat} (xi : fin k -> fin l) (tau : fin l -> tm m_label m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_tm_tm p tau) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_tm id (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_tm {k_label k_tm : nat} {l_label l_tm : nat}
{m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
(xi_tm : fin m_tm -> fin k_tm) (tau_label : fin k_label -> label l_label)
(tau_tm : fin k_tm -> tm l_label l_tm)
(theta_label : fin m_label -> label l_label)
(theta_tm : fin m_tm -> tm l_label l_tm)
(Eq_label : forall x, funcomp tau_label xi_label x = theta_label x)
(Eq_tm : forall x, funcomp tau_tm xi_tm x = theta_tm x) (s : tm m_label m_tm)
{struct s} :
subst_tm tau_label tau_tm (ren_tm xi_label xi_tm s) =
subst_tm theta_label theta_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (compRenSubst_tm (upRen_tm_label (upRen_tm_label xi_label))
           (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_label (up_tm_label tau_label)) (up_tm_tm (up_tm_tm tau_tm))
           (up_tm_label (up_tm_label theta_label))
           (up_tm_tm (up_tm_tm theta_tm))
           (up_ren_subst_tm_label _ _ _
              (up_ren_subst_tm_label _ _ _ Eq_label))
           (up_ren_subst_tm_tm _ _ _ (up_ren_subst_tm_tm _ _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (compRenSubst_tm (upRen_label_label xi_label) (upRen_label_tm xi_tm)
           (up_label_label tau_label) (up_label_tm tau_tm)
           (up_label_label theta_label) (up_label_tm theta_tm)
           (up_ren_subst_label_label _ _ _ Eq_label)
           (up_ren_subst_label_tm _ _ _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_comp
           (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label
              theta_tm Eq_label Eq_tm)
           s1)
  | zero _ _ s0 =>
      congr_zero
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_ren_subst_tm_label _ _ _ Eq_label)
           (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
        (compRenSubst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_ren_subst_tm_label _ _ _ Eq_label)
           (up_ren_subst_tm_tm _ _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_ren_subst_tm_label _ _ _ Eq_label)
           (up_ren_subst_tm_tm _ _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s1)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c
        (compRenSubst_constr xi_label tau_label theta_label Eq_label s0)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s1)
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (compRenSubst_tm xi_label xi_tm tau_label tau_tm theta_label theta_tm
           Eq_label Eq_tm s0)
  end.

Lemma up_subst_ren_label_tm {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (zeta_label : fin l_label -> fin m_label) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_label zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_label_label zeta_label) (upRen_label_tm zeta_tm))
    (up_label_tm sigma) x =
  up_label_tm theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_tm shift id (upRen_label_label zeta_label)
            (upRen_label_tm zeta_tm) (funcomp shift zeta_label)
            (funcomp id zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_tm zeta_label zeta_tm shift id
                  (funcomp shift zeta_label) (funcomp id zeta_tm)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_tm shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_tm_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (zeta_label : fin l_label -> fin m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_tm_label zeta_label)) (up_tm_label sigma) x =
  up_tm_label theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_label id (upRen_tm_label zeta_label)
            (funcomp id zeta_label) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_label zeta_label id (funcomp id zeta_label)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_ren_tm_tm {k : nat} {l_label l_tm : nat} {m_label m_tm : nat}
  (sigma : fin k -> tm l_label l_tm)
  (zeta_label : fin l_label -> fin m_label) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_label zeta_tm) sigma x = theta x) :
  forall x,
  funcomp (ren_tm (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm))
    (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_tm id shift (upRen_tm_label zeta_label)
                (upRen_tm_tm zeta_tm) (funcomp id zeta_label)
                (funcomp shift zeta_tm) (fun x => eq_refl) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_tm zeta_label zeta_tm id shift
                      (funcomp id zeta_label) (funcomp shift zeta_tm)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_label_tm {p : nat} {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (zeta_label : fin l_label -> fin m_label) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_label zeta_tm) sigma x = theta x) :
  forall x,
  funcomp
    (ren_tm (upRen_list_label_label p zeta_label)
       (upRen_list_label_tm p zeta_tm))
    (up_list_label_tm p sigma) x =
  up_list_label_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_tm (shift_p p) id (upRen_list_label_label p zeta_label)
            (upRen_list_label_tm p zeta_tm) (funcomp (shift_p p) zeta_label)
            (funcomp id zeta_tm) (fun x => scons_p_tail' _ _ x)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_tm zeta_label zeta_tm (shift_p p) id
                  (funcomp (shift_p p) zeta_label) (funcomp id zeta_tm)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_tm (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_tm_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (zeta_label : fin l_label -> fin m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_list_tm_label p zeta_label))
    (up_list_tm_label p sigma) x =
  up_list_tm_label p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_label id (upRen_list_tm_label p zeta_label)
            (funcomp id zeta_label) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_label zeta_label id (funcomp id zeta_label)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_tm_tm {p : nat} {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (zeta_label : fin l_label -> fin m_label) (zeta_tm : fin l_tm -> fin m_tm)
  (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (ren_tm zeta_label zeta_tm) sigma x = theta x) :
  forall x,
  funcomp
    (ren_tm (upRen_list_tm_label p zeta_label) (upRen_list_tm_tm p zeta_tm))
    (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_tm m_label (plus p m_tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_tm id (shift_p p)
                  (upRen_list_tm_label p zeta_label)
                  (upRen_list_tm_tm p zeta_tm) (funcomp id zeta_label)
                  (funcomp (shift_p p) zeta_tm) (fun x => eq_refl)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_tm zeta_label zeta_tm id (shift_p p)
                        (funcomp id zeta_label) (funcomp (shift_p p) zeta_tm)
                        (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                  (ap (ren_tm id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_tm {k_label k_tm : nat} {l_label l_tm : nat}
{m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
(sigma_tm : fin m_tm -> tm k_label k_tm)
(zeta_label : fin k_label -> fin l_label) (zeta_tm : fin k_tm -> fin l_tm)
(theta_label : fin m_label -> label l_label)
(theta_tm : fin m_tm -> tm l_label l_tm)
(Eq_label : forall x,
            funcomp (ren_label zeta_label) sigma_label x = theta_label x)
(Eq_tm : forall x,
         funcomp (ren_tm zeta_label zeta_tm) sigma_tm x = theta_tm x)
(s : tm m_label m_tm) {struct s} :
ren_tm zeta_label zeta_tm (subst_tm sigma_label sigma_tm s) =
subst_tm theta_label theta_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (compSubstRen_tm (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm))
           (upRen_tm_label (upRen_tm_label zeta_label))
           (upRen_tm_tm (upRen_tm_tm zeta_tm))
           (up_tm_label (up_tm_label theta_label))
           (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_ren_tm_label _ _ _
              (up_subst_ren_tm_label _ _ _ Eq_label))
           (up_subst_ren_tm_tm _ _ _ _ (up_subst_ren_tm_tm _ _ _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (compSubstRen_tm (up_label_label sigma_label) (up_label_tm sigma_tm)
           (upRen_label_label zeta_label) (upRen_label_tm zeta_tm)
           (up_label_label theta_label) (up_label_tm theta_tm)
           (up_subst_ren_label_label _ _ _ Eq_label)
           (up_subst_ren_label_tm _ _ _ _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_comp
           (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm
              theta_label theta_tm Eq_label Eq_tm)
           s1)
  | zero _ _ s0 =>
      congr_zero
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_ren_tm_label _ _ _ Eq_label)
           (up_subst_ren_tm_tm _ _ _ _ Eq_tm) s1)
        (compSubstRen_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_ren_tm_label _ _ _ Eq_label)
           (up_subst_ren_tm_tm _ _ _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (upRen_tm_label zeta_label) (upRen_tm_tm zeta_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_ren_tm_label _ _ _ Eq_label)
           (up_subst_ren_tm_tm _ _ _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s1)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c
        (compSubstRen_constr sigma_label zeta_label theta_label Eq_label s0)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s1)
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  end.

Lemma up_subst_subst_label_tm {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (tau_label : fin l_label -> label m_label)
  (tau_tm : fin l_tm -> tm m_label m_tm) (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (subst_tm tau_label tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_label_label tau_label) (up_label_tm tau_tm))
    (up_label_tm sigma) x =
  up_label_tm theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_tm shift id (up_label_label tau_label)
            (up_label_tm tau_tm) (funcomp (up_label_label tau_label) shift)
            (funcomp (up_label_tm tau_tm) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_tm tau_label tau_tm shift id
                  (funcomp (ren_label shift) tau_label)
                  (funcomp (ren_tm shift id) tau_tm) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_tm shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_tm_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (tau_label : fin l_label -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_tm_label tau_label)) (up_tm_label sigma) x =
  up_tm_label theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_label id (up_tm_label tau_label)
            (funcomp (up_tm_label tau_label) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_label tau_label id
                  (funcomp (ren_label id) tau_label) (fun x => eq_refl)
                  (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_subst_tm_tm {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (tau_label : fin l_label -> label m_label)
  (tau_tm : fin l_tm -> tm m_label m_tm) (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (subst_tm tau_label tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_tm_label tau_label) (up_tm_tm tau_tm))
    (up_tm_tm sigma) x =
  up_tm_tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_tm id shift (up_tm_label tau_label)
                (up_tm_tm tau_tm) (funcomp (up_tm_label tau_label) id)
                (funcomp (up_tm_tm tau_tm) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_tm tau_label tau_tm id shift
                      (funcomp (ren_label id) tau_label)
                      (funcomp (ren_tm id shift) tau_tm) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_tm id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_label_tm {p : nat} {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (tau_label : fin l_label -> label m_label)
  (tau_tm : fin l_tm -> tm m_label m_tm) (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (subst_tm tau_label tau_tm) sigma x = theta x) :
  forall x,
  funcomp
    (subst_tm (up_list_label_label p tau_label) (up_list_label_tm p tau_tm))
    (up_list_label_tm p sigma) x =
  up_list_label_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_tm (shift_p p) id (up_list_label_label p tau_label)
            (up_list_label_tm p tau_tm)
            (funcomp (up_list_label_label p tau_label) (shift_p p))
            (funcomp (up_list_label_tm p tau_tm) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_tm tau_label tau_tm (shift_p p) id _ _
                  (fun x => eq_sym (scons_p_tail' _ _ x))
                  (fun x => eq_sym eq_refl) (sigma n)))
            (ap (ren_tm (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_tm_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (tau_label : fin l_label -> label m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_list_tm_label p tau_label))
    (up_list_tm_label p sigma) x =
  up_list_tm_label p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_label id (up_list_tm_label p tau_label)
            (funcomp (up_list_tm_label p tau_label) id) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_label tau_label id _ (fun x => eq_sym eq_refl)
                  (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_tm_tm {p : nat} {k : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma : fin k -> tm l_label l_tm)
  (tau_label : fin l_label -> label m_label)
  (tau_tm : fin l_tm -> tm m_label m_tm) (theta : fin k -> tm m_label m_tm)
  (Eq : forall x, funcomp (subst_tm tau_label tau_tm) sigma x = theta x) :
  forall x,
  funcomp (subst_tm (up_list_tm_label p tau_label) (up_list_tm_tm p tau_tm))
    (up_list_tm_tm p sigma) x =
  up_list_tm_tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_tm l_label (plus p l_tm)) (zero_p p)) _
            _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_tm id (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_tm id (shift_p p) (up_list_tm_label p tau_label)
                  (up_list_tm_tm p tau_tm)
                  (funcomp (up_list_tm_label p tau_label) id)
                  (funcomp (up_list_tm_tm p tau_tm) (shift_p p))
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_tm tau_label tau_tm id (shift_p p) _ _
                        (fun x => eq_sym eq_refl)
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_tm id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_tm {k_label k_tm : nat} {l_label l_tm : nat}
{m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
(sigma_tm : fin m_tm -> tm k_label k_tm)
(tau_label : fin k_label -> label l_label)
(tau_tm : fin k_tm -> tm l_label l_tm)
(theta_label : fin m_label -> label l_label)
(theta_tm : fin m_tm -> tm l_label l_tm)
(Eq_label : forall x,
            funcomp (subst_label tau_label) sigma_label x = theta_label x)
(Eq_tm : forall x,
         funcomp (subst_tm tau_label tau_tm) sigma_tm x = theta_tm x)
(s : tm m_label m_tm) {struct s} :
subst_tm tau_label tau_tm (subst_tm sigma_label sigma_tm s) =
subst_tm theta_label theta_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (compSubstSubst_tm (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm))
           (up_tm_label (up_tm_label tau_label)) (up_tm_tm (up_tm_tm tau_tm))
           (up_tm_label (up_tm_label theta_label))
           (up_tm_tm (up_tm_tm theta_tm))
           (up_subst_subst_tm_label _ _ _
              (up_subst_subst_tm_label _ _ _ Eq_label))
           (up_subst_subst_tm_tm _ _ _ _ (up_subst_subst_tm_tm _ _ _ _ Eq_tm))
           s0)
  | tlam _ _ s0 =>
      congr_tlam
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (compSubstSubst_tm (up_label_label sigma_label)
           (up_label_tm sigma_tm) (up_label_label tau_label)
           (up_label_tm tau_tm) (up_label_label theta_label)
           (up_label_tm theta_tm) (up_subst_subst_label_label _ _ _ Eq_label)
           (up_subst_subst_label_tm _ _ _ _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_comp
           (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm
              theta_label theta_tm Eq_label Eq_tm)
           s1)
  | zero _ _ s0 =>
      congr_zero
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_subst_tm_label _ _ _ Eq_label)
           (up_subst_subst_tm_tm _ _ _ _ Eq_tm) s1)
        (compSubstSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_subst_tm_label _ _ _ Eq_label)
           (up_subst_subst_tm_tm _ _ _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (up_tm_label tau_label) (up_tm_tm tau_tm)
           (up_tm_label theta_label) (up_tm_tm theta_tm)
           (up_subst_subst_tm_label _ _ _ Eq_label)
           (up_subst_subst_tm_tm _ _ _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s1)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c
        (compSubstSubst_constr sigma_label tau_label theta_label Eq_label s0)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s1)
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm theta_label
           theta_tm Eq_label Eq_tm s0)
  end.

Lemma renRen_tm {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
  (xi_tm : fin m_tm -> fin k_tm) (zeta_label : fin k_label -> fin l_label)
  (zeta_tm : fin k_tm -> fin l_tm) (s : tm m_label m_tm) :
  ren_tm zeta_label zeta_tm (ren_tm xi_label xi_tm s) =
  ren_tm (funcomp zeta_label xi_label) (funcomp zeta_tm xi_tm) s.
Proof.
exact (compRenRen_tm xi_label xi_tm zeta_label zeta_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_tm_pointwise {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
  (xi_tm : fin m_tm -> fin k_tm) (zeta_label : fin k_label -> fin l_label)
  (zeta_tm : fin k_tm -> fin l_tm) :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_label zeta_tm) (ren_tm xi_label xi_tm))
    (ren_tm (funcomp zeta_label xi_label) (funcomp zeta_tm xi_tm)).
Proof.
exact (fun s =>
       compRenRen_tm xi_label xi_tm zeta_label zeta_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
  (xi_tm : fin m_tm -> fin k_tm) (tau_label : fin k_label -> label l_label)
  (tau_tm : fin k_tm -> tm l_label l_tm) (s : tm m_label m_tm) :
  subst_tm tau_label tau_tm (ren_tm xi_label xi_tm s) =
  subst_tm (funcomp tau_label xi_label) (funcomp tau_tm xi_tm) s.
Proof.
exact (compRenSubst_tm xi_label xi_tm tau_label tau_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_tm_pointwise {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (xi_label : fin m_label -> fin k_label)
  (xi_tm : fin m_tm -> fin k_tm) (tau_label : fin k_label -> label l_label)
  (tau_tm : fin k_tm -> tm l_label l_tm) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_label tau_tm) (ren_tm xi_label xi_tm))
    (subst_tm (funcomp tau_label xi_label) (funcomp tau_tm xi_tm)).
Proof.
exact (fun s =>
       compRenSubst_tm xi_label xi_tm tau_label tau_tm _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_tm {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_tm : fin m_tm -> tm k_label k_tm)
  (zeta_label : fin k_label -> fin l_label) (zeta_tm : fin k_tm -> fin l_tm)
  (s : tm m_label m_tm) :
  ren_tm zeta_label zeta_tm (subst_tm sigma_label sigma_tm s) =
  subst_tm (funcomp (ren_label zeta_label) sigma_label)
    (funcomp (ren_tm zeta_label zeta_tm) sigma_tm) s.
Proof.
exact (compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_tm_pointwise {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_tm : fin m_tm -> tm k_label k_tm)
  (zeta_label : fin k_label -> fin l_label) (zeta_tm : fin k_tm -> fin l_tm)
  :
  pointwise_relation _ eq
    (funcomp (ren_tm zeta_label zeta_tm) (subst_tm sigma_label sigma_tm))
    (subst_tm (funcomp (ren_label zeta_label) sigma_label)
       (funcomp (ren_tm zeta_label zeta_tm) sigma_tm)).
Proof.
exact (fun s =>
       compSubstRen_tm sigma_label sigma_tm zeta_label zeta_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_tm : fin m_tm -> tm k_label k_tm)
  (tau_label : fin k_label -> label l_label)
  (tau_tm : fin k_tm -> tm l_label l_tm) (s : tm m_label m_tm) :
  subst_tm tau_label tau_tm (subst_tm sigma_label sigma_tm s) =
  subst_tm (funcomp (subst_label tau_label) sigma_label)
    (funcomp (subst_tm tau_label tau_tm) sigma_tm) s.
Proof.
exact (compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_tm_pointwise {k_label k_tm : nat} {l_label l_tm : nat}
  {m_label m_tm : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_tm : fin m_tm -> tm k_label k_tm)
  (tau_label : fin k_label -> label l_label)
  (tau_tm : fin k_tm -> tm l_label l_tm) :
  pointwise_relation _ eq
    (funcomp (subst_tm tau_label tau_tm) (subst_tm sigma_label sigma_tm))
    (subst_tm (funcomp (subst_label tau_label) sigma_label)
       (funcomp (subst_tm tau_label tau_tm) sigma_tm)).
Proof.
exact (fun s =>
       compSubstSubst_tm sigma_label sigma_tm tau_label tau_tm _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_label_tm {m : nat} {n_label n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_label n_tm)
  (Eq : forall x, funcomp (var_tm n_label n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (S n_label) n_tm) (upRen_label_tm xi) x =
  up_label_tm sigma x.
Proof.
exact (fun n => ap (ren_tm shift id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_label {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label n_label) (upRen_tm_label xi) x = up_tm_label sigma x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma rinstInst_up_tm_tm {m : nat} {n_label n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_label n_tm)
  (Eq : forall x, funcomp (var_tm n_label n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_label (S n_tm)) (upRen_tm_tm xi) x = up_tm_tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_tm id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_label_tm {p : nat} {m : nat} {n_label n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_label n_tm)
  (Eq : forall x, funcomp (var_tm n_label n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm (plus p n_label) n_tm) (upRen_list_label_tm p xi) x =
  up_list_label_tm p sigma x.
Proof.
exact (fun n => ap (ren_tm (shift_p p) id) (Eq n)).
Qed.

Lemma rinstInst_up_list_tm_label {p : nat} {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label n_label) (upRen_list_tm_label p xi) x =
  up_list_tm_label p sigma x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma rinstInst_up_list_tm_tm {p : nat} {m : nat} {n_label n_tm : nat}
  (xi : fin m -> fin n_tm) (sigma : fin m -> tm n_label n_tm)
  (Eq : forall x, funcomp (var_tm n_label n_tm) xi x = sigma x) :
  forall x,
  funcomp (var_tm n_label (plus p n_tm)) (upRen_list_tm_tm p xi) x =
  up_list_tm_tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_tm n_label (plus p n_tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_tm id (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_tm {m_label m_tm : nat} {n_label n_tm : nat}
(xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm)
(sigma_label : fin m_label -> label n_label)
(sigma_tm : fin m_tm -> tm n_label n_tm)
(Eq_label : forall x, funcomp (var_label n_label) xi_label x = sigma_label x)
(Eq_tm : forall x, funcomp (var_tm n_label n_tm) xi_tm x = sigma_tm x)
(s : tm m_label m_tm) {struct s} :
ren_tm xi_label xi_tm s = subst_tm sigma_label sigma_tm s :=
  match s with
  | var_tm _ _ s0 => Eq_tm s0
  | error _ _ => congr_error
  | skip _ _ => congr_skip
  | bitstring _ _ s0 => congr_bitstring (eq_refl s0)
  | loc _ _ s0 => congr_loc (eq_refl s0)
  | fixlam _ _ s0 =>
      congr_fixlam
        (rinst_inst_tm (upRen_tm_label (upRen_tm_label xi_label))
           (upRen_tm_tm (upRen_tm_tm xi_tm))
           (up_tm_label (up_tm_label sigma_label))
           (up_tm_tm (up_tm_tm sigma_tm))
           (rinstInst_up_tm_label _ _ (rinstInst_up_tm_label _ _ Eq_label))
           (rinstInst_up_tm_tm _ _ (rinstInst_up_tm_tm _ _ Eq_tm)) s0)
  | tlam _ _ s0 =>
      congr_tlam
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | l_lam _ _ s0 =>
      congr_l_lam
        (rinst_inst_tm (upRen_label_label xi_label) (upRen_label_tm xi_tm)
           (up_label_label sigma_label) (up_label_tm sigma_tm)
           (rinstInst_up_label_label _ _ Eq_label)
           (rinstInst_up_label_tm _ _ Eq_tm) s0)
  | Op _ _ s0 s1 =>
      congr_Op (eq_refl s0)
        (list_ext
           (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm)
           s1)
  | zero _ _ s0 =>
      congr_zero
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | app _ _ s0 s1 =>
      congr_app
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | alloc _ _ s0 =>
      congr_alloc
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | dealloc _ _ s0 =>
      congr_dealloc
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | assign _ _ s0 s1 =>
      congr_assign
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | tm_pair _ _ s0 s1 =>
      congr_tm_pair
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s1)
  | left_tm _ _ s0 =>
      congr_left_tm
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | right_tm _ _ s0 =>
      congr_right_tm
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | inl _ _ s0 =>
      congr_inl
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | inr _ _ s0 =>
      congr_inr
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | case _ _ s0 s1 s2 =>
      congr_case
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_label _ _ Eq_label)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
        (rinst_inst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_label _ _ Eq_label)
           (rinstInst_up_tm_tm _ _ Eq_tm) s2)
  | tapp _ _ s0 =>
      congr_tapp
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | lapp _ _ s0 s1 =>
      congr_lapp
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_label xi_label sigma_label Eq_label s1)
  | pack _ _ s0 =>
      congr_pack
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  | unpack _ _ s0 s1 =>
      congr_unpack
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm (upRen_tm_label xi_label) (upRen_tm_tm xi_tm)
           (up_tm_label sigma_label) (up_tm_tm sigma_tm)
           (rinstInst_up_tm_label _ _ Eq_label)
           (rinstInst_up_tm_tm _ _ Eq_tm) s1)
  | if_tm _ _ s0 s1 s2 =>
      congr_if_tm
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s1)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s2)
  | if_c _ _ s0 s1 s2 =>
      congr_if_c (rinst_inst_constr xi_label sigma_label Eq_label s0)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s1)
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s2)
  | sync _ _ s0 =>
      congr_sync
        (rinst_inst_tm xi_label xi_tm sigma_label sigma_tm Eq_label Eq_tm s0)
  end.

Lemma rinstInst'_tm {m_label m_tm : nat} {n_label n_tm : nat}
  (xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm)
  (s : tm m_label m_tm) :
  ren_tm xi_label xi_tm s =
  subst_tm (funcomp (var_label n_label) xi_label)
    (funcomp (var_tm n_label n_tm) xi_tm) s.
Proof.
exact (rinst_inst_tm xi_label xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstInst'_tm_pointwise {m_label m_tm : nat} {n_label n_tm : nat}
  (xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq (ren_tm xi_label xi_tm)
    (subst_tm (funcomp (var_label n_label) xi_label)
       (funcomp (var_tm n_label n_tm) xi_tm)).
Proof.
exact (fun s =>
       rinst_inst_tm xi_label xi_tm _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma instId'_tm {m_label m_tm : nat} (s : tm m_label m_tm) :
  subst_tm (var_label m_label) (var_tm m_label m_tm) s = s.
Proof.
exact (idSubst_tm (var_label m_label) (var_tm m_label m_tm)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_tm_pointwise {m_label m_tm : nat} :
  pointwise_relation _ eq
    (subst_tm (var_label m_label) (var_tm m_label m_tm)) id.
Proof.
exact (fun s =>
       idSubst_tm (var_label m_label) (var_tm m_label m_tm)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_tm {m_label m_tm : nat} (s : tm m_label m_tm) :
  ren_tm id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma rinstId'_tm_pointwise {m_label m_tm : nat} :
  pointwise_relation _ eq (@ren_tm m_label m_tm m_label m_tm id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_tm s) (rinstInst'_tm id id s)).
Qed.

Lemma varL'_tm {m_label m_tm : nat} {n_label n_tm : nat}
  (sigma_label : fin m_label -> label n_label)
  (sigma_tm : fin m_tm -> tm n_label n_tm) (x : fin m_tm) :
  subst_tm sigma_label sigma_tm (var_tm m_label m_tm x) = sigma_tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_tm_pointwise {m_label m_tm : nat} {n_label n_tm : nat}
  (sigma_label : fin m_label -> label n_label)
  (sigma_tm : fin m_tm -> tm n_label n_tm) :
  pointwise_relation _ eq
    (funcomp (subst_tm sigma_label sigma_tm) (var_tm m_label m_tm)) sigma_tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_tm {m_label m_tm : nat} {n_label n_tm : nat}
  (xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm)
  (x : fin m_tm) :
  ren_tm xi_label xi_tm (var_tm m_label m_tm x) =
  var_tm n_label n_tm (xi_tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_tm_pointwise {m_label m_tm : nat} {n_label n_tm : nat}
  (xi_label : fin m_label -> fin n_label) (xi_tm : fin m_tm -> fin n_tm) :
  pointwise_relation _ eq
    (funcomp (ren_tm xi_label xi_tm) (var_tm m_label m_tm))
    (funcomp (var_tm n_label n_tm) xi_tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive ty (n_label n_ty : nat) : Type :=
  | var_ty : fin n_ty -> ty n_label n_ty
  | Any : ty n_label n_ty
  | Unit : ty n_label n_ty
  | Data : label n_label -> ty n_label n_ty
  | Ref : ty n_label n_ty -> ty n_label n_ty
  | arr : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
  | prod : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
  | sum : ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty
  | all : ty n_label n_ty -> ty n_label (S n_ty) -> ty n_label n_ty
  | ex : ty n_label n_ty -> ty n_label (S n_ty) -> ty n_label n_ty
  | all_l :
      cond_sym -> label n_label -> ty (S n_label) n_ty -> ty n_label n_ty
  | t_if :
      constr n_label -> ty n_label n_ty -> ty n_label n_ty -> ty n_label n_ty.

Lemma congr_Any {m_label m_ty : nat} : Any m_label m_ty = Any m_label m_ty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Unit {m_label m_ty : nat} : Unit m_label m_ty = Unit m_label m_ty.
Proof.
exact (eq_refl).
Qed.

Lemma congr_Data {m_label m_ty : nat} {s0 : label m_label}
  {t0 : label m_label} (H0 : s0 = t0) :
  Data m_label m_ty s0 = Data m_label m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Data m_label m_ty x) H0)).
Qed.

Lemma congr_Ref {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {t0 : ty m_label m_ty} (H0 : s0 = t0) :
  Ref m_label m_ty s0 = Ref m_label m_ty t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => Ref m_label m_ty x) H0)).
Qed.

Lemma congr_arr {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {s1 : ty m_label m_ty} {t0 : ty m_label m_ty} {t1 : ty m_label m_ty}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  arr m_label m_ty s0 s1 = arr m_label m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => arr m_label m_ty x s1) H0))
         (ap (fun x => arr m_label m_ty t0 x) H1)).
Qed.

Lemma congr_prod {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {s1 : ty m_label m_ty} {t0 : ty m_label m_ty} {t1 : ty m_label m_ty}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  prod m_label m_ty s0 s1 = prod m_label m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => prod m_label m_ty x s1) H0))
         (ap (fun x => prod m_label m_ty t0 x) H1)).
Qed.

Lemma congr_sum {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {s1 : ty m_label m_ty} {t0 : ty m_label m_ty} {t1 : ty m_label m_ty}
  (H0 : s0 = t0) (H1 : s1 = t1) :
  sum m_label m_ty s0 s1 = sum m_label m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => sum m_label m_ty x s1) H0))
         (ap (fun x => sum m_label m_ty t0 x) H1)).
Qed.

Lemma congr_all {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {s1 : ty m_label (S m_ty)} {t0 : ty m_label m_ty}
  {t1 : ty m_label (S m_ty)} (H0 : s0 = t0) (H1 : s1 = t1) :
  all m_label m_ty s0 s1 = all m_label m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => all m_label m_ty x s1) H0))
         (ap (fun x => all m_label m_ty t0 x) H1)).
Qed.

Lemma congr_ex {m_label m_ty : nat} {s0 : ty m_label m_ty}
  {s1 : ty m_label (S m_ty)} {t0 : ty m_label m_ty}
  {t1 : ty m_label (S m_ty)} (H0 : s0 = t0) (H1 : s1 = t1) :
  ex m_label m_ty s0 s1 = ex m_label m_ty t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ex m_label m_ty x s1) H0))
         (ap (fun x => ex m_label m_ty t0 x) H1)).
Qed.

Lemma congr_all_l {m_label m_ty : nat} {s0 : cond_sym} {s1 : label m_label}
  {s2 : ty (S m_label) m_ty} {t0 : cond_sym} {t1 : label m_label}
  {t2 : ty (S m_label) m_ty} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  all_l m_label m_ty s0 s1 s2 = all_l m_label m_ty t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => all_l m_label m_ty x s1 s2) H0))
            (ap (fun x => all_l m_label m_ty t0 x s2) H1))
         (ap (fun x => all_l m_label m_ty t0 t1 x) H2)).
Qed.

Lemma congr_t_if {m_label m_ty : nat} {s0 : constr m_label}
  {s1 : ty m_label m_ty} {s2 : ty m_label m_ty} {t0 : constr m_label}
  {t1 : ty m_label m_ty} {t2 : ty m_label m_ty} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) : t_if m_label m_ty s0 s1 s2 = t_if m_label m_ty t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => t_if m_label m_ty x s1 s2) H0))
            (ap (fun x => t_if m_label m_ty t0 x s2) H1))
         (ap (fun x => t_if m_label m_ty t0 t1 x) H2)).
Qed.

Lemma upRen_label_ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_ty_label {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_label_ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_ty_label (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n)
  : fin m -> fin n.
Proof.
exact (xi).
Defined.

Lemma upRen_list_ty_ty (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_ty {m_label m_ty : nat} {n_label n_ty : nat}
(xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty)
(s : ty m_label m_ty) {struct s} : ty n_label n_ty :=
  match s with
  | var_ty _ _ s0 => var_ty n_label n_ty (xi_ty s0)
  | Any _ _ => Any n_label n_ty
  | Unit _ _ => Unit n_label n_ty
  | Data _ _ s0 => Data n_label n_ty (ren_label xi_label s0)
  | Ref _ _ s0 => Ref n_label n_ty (ren_ty xi_label xi_ty s0)
  | arr _ _ s0 s1 =>
      arr n_label n_ty (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | prod _ _ s0 s1 =>
      prod n_label n_ty (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | sum _ _ s0 s1 =>
      sum n_label n_ty (ren_ty xi_label xi_ty s0) (ren_ty xi_label xi_ty s1)
  | all _ _ s0 s1 =>
      all n_label n_ty (ren_ty xi_label xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty) s1)
  | ex _ _ s0 s1 =>
      ex n_label n_ty (ren_ty xi_label xi_ty s0)
        (ren_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      all_l n_label n_ty s0 (ren_label xi_label s1)
        (ren_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      t_if n_label n_ty (ren_constr xi_label s0) (ren_ty xi_label xi_ty s1)
        (ren_ty xi_label xi_ty s2)
  end.

Lemma up_label_ty {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) : fin m -> ty (S n_label) n_ty.
Proof.
exact (funcomp (ren_ty shift id) sigma).
Defined.

Lemma up_ty_label {m : nat} {n_label : nat} (sigma : fin m -> label n_label)
  : fin m -> label n_label.
Proof.
exact (funcomp (ren_label id) sigma).
Defined.

Lemma up_ty_ty {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) : fin (S m) -> ty n_label (S n_ty).
Proof.
exact (scons (var_ty n_label (S n_ty) var_zero)
         (funcomp (ren_ty id shift) sigma)).
Defined.

Lemma up_list_label_ty (p : nat) {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) : fin m -> ty (plus p n_label) n_ty.
Proof.
exact (funcomp (ren_ty (shift_p p) id) sigma).
Defined.

Lemma up_list_ty_label (p : nat) {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) : fin m -> label n_label.
Proof.
exact (funcomp (ren_label id) sigma).
Defined.

Lemma up_list_ty_ty (p : nat) {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) :
  fin (plus p m) -> ty n_label (plus p n_ty).
Proof.
exact (scons_p p (funcomp (var_ty n_label (plus p n_ty)) (zero_p p))
         (funcomp (ren_ty id (shift_p p)) sigma)).
Defined.

Fixpoint subst_ty {m_label m_ty : nat} {n_label n_ty : nat}
(sigma_label : fin m_label -> label n_label)
(sigma_ty : fin m_ty -> ty n_label n_ty) (s : ty m_label m_ty) {struct s} :
ty n_label n_ty :=
  match s with
  | var_ty _ _ s0 => sigma_ty s0
  | Any _ _ => Any n_label n_ty
  | Unit _ _ => Unit n_label n_ty
  | Data _ _ s0 => Data n_label n_ty (subst_label sigma_label s0)
  | Ref _ _ s0 => Ref n_label n_ty (subst_ty sigma_label sigma_ty s0)
  | arr _ _ s0 s1 =>
      arr n_label n_ty (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | prod _ _ s0 s1 =>
      prod n_label n_ty (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | sum _ _ s0 s1 =>
      sum n_label n_ty (subst_ty sigma_label sigma_ty s0)
        (subst_ty sigma_label sigma_ty s1)
  | all _ _ s0 s1 =>
      all n_label n_ty (subst_ty sigma_label sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty) s1)
  | ex _ _ s0 s1 =>
      ex n_label n_ty (subst_ty sigma_label sigma_ty s0)
        (subst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      all_l n_label n_ty s0 (subst_label sigma_label s1)
        (subst_ty (up_label_label sigma_label) (up_label_ty sigma_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      t_if n_label n_ty (subst_constr sigma_label s0)
        (subst_ty sigma_label sigma_ty s1) (subst_ty sigma_label sigma_ty s2)
  end.

Lemma upId_label_ty {m_label m_ty : nat}
  (sigma : fin m_ty -> ty m_label m_ty)
  (Eq : forall x, sigma x = var_ty m_label m_ty x) :
  forall x, up_label_ty sigma x = var_ty (S m_label) m_ty x.
Proof.
exact (fun n => ap (ren_ty shift id) (Eq n)).
Qed.

Lemma upId_ty_label {m_label : nat} (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_ty_label sigma x = var_label m_label x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upId_ty_ty {m_label m_ty : nat} (sigma : fin m_ty -> ty m_label m_ty)
  (Eq : forall x, sigma x = var_ty m_label m_ty x) :
  forall x, up_ty_ty sigma x = var_ty m_label (S m_ty) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_label_ty {p : nat} {m_label m_ty : nat}
  (sigma : fin m_ty -> ty m_label m_ty)
  (Eq : forall x, sigma x = var_ty m_label m_ty x) :
  forall x, up_list_label_ty p sigma x = var_ty (plus p m_label) m_ty x.
Proof.
exact (fun n => ap (ren_ty (shift_p p) id) (Eq n)).
Qed.

Lemma upId_list_ty_label {p : nat} {m_label : nat}
  (sigma : fin m_label -> label m_label)
  (Eq : forall x, sigma x = var_label m_label x) :
  forall x, up_list_ty_label p sigma x = var_label m_label x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upId_list_ty_ty {p : nat} {m_label m_ty : nat}
  (sigma : fin m_ty -> ty m_label m_ty)
  (Eq : forall x, sigma x = var_ty m_label m_ty x) :
  forall x, up_list_ty_ty p sigma x = var_ty m_label (plus p m_ty) x.
Proof.
exact (fun n =>
       scons_p_eta (var_ty m_label (plus p m_ty))
         (fun n => ap (ren_ty id (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_ty {m_label m_ty : nat}
(sigma_label : fin m_label -> label m_label)
(sigma_ty : fin m_ty -> ty m_label m_ty)
(Eq_label : forall x, sigma_label x = var_label m_label x)
(Eq_ty : forall x, sigma_ty x = var_ty m_label m_ty x) (s : ty m_label m_ty)
{struct s} : subst_ty sigma_label sigma_ty s = s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 => congr_Data (idSubst_label sigma_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (idSubst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (upId_ty_label _ Eq_label) (upId_ty_ty _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (idSubst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (upId_ty_label _ Eq_label) (upId_ty_ty _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0) (idSubst_label sigma_label Eq_label s1)
        (idSubst_ty (up_label_label sigma_label) (up_label_ty sigma_ty)
           (upId_label_label _ Eq_label) (upId_label_ty _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if (idSubst_constr sigma_label Eq_label s0)
        (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s1)
        (idSubst_ty sigma_label sigma_ty Eq_label Eq_ty s2)
  end.

Lemma upExtRen_label_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_label_ty xi x = upRen_label_ty zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_ty_label {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_label xi x = upRen_ty_label zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_ty_ty {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ty_ty xi x = upRen_ty_ty zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_label_ty {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_label_ty p xi x = upRen_list_label_ty p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_ty_label {p : nat} {m : nat} {n : nat}
  (xi : fin m -> fin n) (zeta : fin m -> fin n)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_label p xi x = upRen_list_ty_label p zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_list_ty_ty {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_ty_ty p xi x = upRen_list_ty_ty p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_ty {m_label m_ty : nat} {n_label n_ty : nat}
(xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty)
(zeta_label : fin m_label -> fin n_label) (zeta_ty : fin m_ty -> fin n_ty)
(Eq_label : forall x, xi_label x = zeta_label x)
(Eq_ty : forall x, xi_ty x = zeta_ty x) (s : ty m_label m_ty) {struct s} :
ren_ty xi_label xi_ty s = ren_ty zeta_label zeta_ty s :=
  match s with
  | var_ty _ _ s0 => ap (var_ty n_label n_ty) (Eq_ty s0)
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 => congr_Data (extRen_label xi_label zeta_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
        (extRen_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_label _ _ Eq_label) (upExtRen_ty_ty _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s0)
        (extRen_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (upExtRen_ty_label _ _ Eq_label) (upExtRen_ty_ty _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0) (extRen_label xi_label zeta_label Eq_label s1)
        (extRen_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty)
           (upRen_label_label zeta_label) (upRen_label_ty zeta_ty)
           (upExtRen_label_label _ _ Eq_label) (upExtRen_label_ty _ _ Eq_ty)
           s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if (extRen_constr xi_label zeta_label Eq_label s0)
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s1)
        (extRen_ty xi_label xi_ty zeta_label zeta_ty Eq_label Eq_ty s2)
  end.

Lemma upExt_label_ty {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) (tau : fin m -> ty n_label n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_label_ty sigma x = up_label_ty tau x.
Proof.
exact (fun n => ap (ren_ty shift id) (Eq n)).
Qed.

Lemma upExt_ty_label {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_label sigma x = up_ty_label tau x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upExt_ty_ty {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) (tau : fin m -> ty n_label n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ty_ty sigma x = up_ty_ty tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_label_ty {p : nat} {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) (tau : fin m -> ty n_label n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_label_ty p sigma x = up_list_label_ty p tau x.
Proof.
exact (fun n => ap (ren_ty (shift_p p) id) (Eq n)).
Qed.

Lemma upExt_list_ty_label {p : nat} {m : nat} {n_label : nat}
  (sigma : fin m -> label n_label) (tau : fin m -> label n_label)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_label p sigma x = up_list_ty_label p tau x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma upExt_list_ty_ty {p : nat} {m : nat} {n_label n_ty : nat}
  (sigma : fin m -> ty n_label n_ty) (tau : fin m -> ty n_label n_ty)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_ty_ty p sigma x = up_list_ty_ty p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_ty id (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_ty {m_label m_ty : nat} {n_label n_ty : nat}
(sigma_label : fin m_label -> label n_label)
(sigma_ty : fin m_ty -> ty n_label n_ty)
(tau_label : fin m_label -> label n_label)
(tau_ty : fin m_ty -> ty n_label n_ty)
(Eq_label : forall x, sigma_label x = tau_label x)
(Eq_ty : forall x, sigma_ty x = tau_ty x) (s : ty m_label m_ty) {struct s} :
subst_ty sigma_label sigma_ty s = subst_ty tau_label tau_ty s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 => congr_Data (ext_label sigma_label tau_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
        (ext_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (upExt_ty_label _ _ Eq_label) (upExt_ty_ty _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s0)
        (ext_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (upExt_ty_label _ _ Eq_label) (upExt_ty_ty _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0) (ext_label sigma_label tau_label Eq_label s1)
        (ext_ty (up_label_label sigma_label) (up_label_ty sigma_ty)
           (up_label_label tau_label) (up_label_ty tau_ty)
           (upExt_label_label _ _ Eq_label) (upExt_label_ty _ _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if (ext_constr sigma_label tau_label Eq_label s0)
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s1)
        (ext_ty sigma_label sigma_ty tau_label tau_ty Eq_label Eq_ty s2)
  end.

Lemma up_ren_ren_label_ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_label_ty zeta) (upRen_label_ty xi) x = upRen_label_ty rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_ty_label {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_ty_label zeta) (upRen_ty_label xi) x = upRen_ty_label rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_ty_ty {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_ty_ty zeta) (upRen_ty_ty xi) x = upRen_ty_ty rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_label_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_label_ty p zeta) (upRen_list_label_ty p xi) x =
  upRen_list_label_ty p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_ty_label {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_label p zeta) (upRen_list_ty_label p xi) x =
  upRen_list_ty_label p rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_list_ty_ty {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_ty_ty p zeta) (upRen_list_ty_ty p xi) x =
  upRen_list_ty_ty p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_ty {k_label k_ty : nat} {l_label l_ty : nat}
{m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
(xi_ty : fin m_ty -> fin k_ty) (zeta_label : fin k_label -> fin l_label)
(zeta_ty : fin k_ty -> fin l_ty) (rho_label : fin m_label -> fin l_label)
(rho_ty : fin m_ty -> fin l_ty)
(Eq_label : forall x, funcomp zeta_label xi_label x = rho_label x)
(Eq_ty : forall x, funcomp zeta_ty xi_ty x = rho_ty x) (s : ty m_label m_ty)
{struct s} :
ren_ty zeta_label zeta_ty (ren_ty xi_label xi_ty s) =
ren_ty rho_label rho_ty s :=
  match s with
  | var_ty _ _ s0 => ap (var_ty l_label l_ty) (Eq_ty s0)
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 =>
      congr_Data (compRenRen_label xi_label zeta_label rho_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
        (compRenRen_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (upRen_ty_label rho_label) (upRen_ty_ty rho_ty) Eq_label
           (up_ren_ren _ _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s0)
        (compRenRen_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (upRen_ty_label rho_label) (upRen_ty_ty rho_ty) Eq_label
           (up_ren_ren _ _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0)
        (compRenRen_label xi_label zeta_label rho_label Eq_label s1)
        (compRenRen_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty)
           (upRen_label_label zeta_label) (upRen_label_ty zeta_ty)
           (upRen_label_label rho_label) (upRen_label_ty rho_ty)
           (up_ren_ren _ _ _ Eq_label) Eq_ty s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if
        (compRenRen_constr xi_label zeta_label rho_label Eq_label s0)
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s1)
        (compRenRen_ty xi_label xi_ty zeta_label zeta_ty rho_label rho_ty
           Eq_label Eq_ty s2)
  end.

Lemma up_ren_subst_label_ty {k : nat} {l : nat} {m_label m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_label m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_label_ty tau) (upRen_label_ty xi) x = up_label_ty theta x.
Proof.
exact (fun n => ap (ren_ty shift id) (Eq n)).
Qed.

Lemma up_ren_subst_ty_label {k : nat} {l : nat} {m_label : nat}
  (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_ty_label tau) (upRen_ty_label xi) x = up_ty_label theta x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma up_ren_subst_ty_ty {k : nat} {l : nat} {m_label m_ty : nat}
  (xi : fin k -> fin l) (tau : fin l -> ty m_label m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_ty_ty tau) (upRen_ty_ty xi) x = up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_label_ty {p : nat} {k : nat} {l : nat}
  {m_label m_ty : nat} (xi : fin k -> fin l) (tau : fin l -> ty m_label m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_label_ty p tau) (upRen_list_label_ty p xi) x =
  up_list_label_ty p theta x.
Proof.
exact (fun n => ap (ren_ty (shift_p p) id) (Eq n)).
Qed.

Lemma up_ren_subst_list_ty_label {p : nat} {k : nat} {l : nat}
  {m_label : nat} (xi : fin k -> fin l) (tau : fin l -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_ty_label p tau) (upRen_list_ty_label p xi) x =
  up_list_ty_label p theta x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma up_ren_subst_list_ty_ty {p : nat} {k : nat} {l : nat}
  {m_label m_ty : nat} (xi : fin k -> fin l) (tau : fin l -> ty m_label m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_ty_ty p tau) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_ty id (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_ty {k_label k_ty : nat} {l_label l_ty : nat}
{m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
(xi_ty : fin m_ty -> fin k_ty) (tau_label : fin k_label -> label l_label)
(tau_ty : fin k_ty -> ty l_label l_ty)
(theta_label : fin m_label -> label l_label)
(theta_ty : fin m_ty -> ty l_label l_ty)
(Eq_label : forall x, funcomp tau_label xi_label x = theta_label x)
(Eq_ty : forall x, funcomp tau_ty xi_ty x = theta_ty x) (s : ty m_label m_ty)
{struct s} :
subst_ty tau_label tau_ty (ren_ty xi_label xi_ty s) =
subst_ty theta_label theta_ty s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 =>
      congr_Data
        (compRenSubst_label xi_label tau_label theta_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
        (compRenSubst_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_ren_subst_ty_label _ _ _ Eq_label)
           (up_ren_subst_ty_ty _ _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s0)
        (compRenSubst_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_ren_subst_ty_label _ _ _ Eq_label)
           (up_ren_subst_ty_ty _ _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0)
        (compRenSubst_label xi_label tau_label theta_label Eq_label s1)
        (compRenSubst_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty)
           (up_label_label tau_label) (up_label_ty tau_ty)
           (up_label_label theta_label) (up_label_ty theta_ty)
           (up_ren_subst_label_label _ _ _ Eq_label)
           (up_ren_subst_label_ty _ _ _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if
        (compRenSubst_constr xi_label tau_label theta_label Eq_label s0)
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s1)
        (compRenSubst_ty xi_label xi_ty tau_label tau_ty theta_label theta_ty
           Eq_label Eq_ty s2)
  end.

Lemma up_subst_ren_label_ty {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (zeta_label : fin l_label -> fin m_label) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_label zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_label_label zeta_label) (upRen_label_ty zeta_ty))
    (up_label_ty sigma) x =
  up_label_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty shift id (upRen_label_label zeta_label)
            (upRen_label_ty zeta_ty) (funcomp shift zeta_label)
            (funcomp id zeta_ty) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_label zeta_ty shift id
                  (funcomp shift zeta_label) (funcomp id zeta_ty)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_ty shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_ty_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (zeta_label : fin l_label -> fin m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_ty_label zeta_label)) (up_ty_label sigma) x =
  up_ty_label theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_label id (upRen_ty_label zeta_label)
            (funcomp id zeta_label) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_label zeta_label id (funcomp id zeta_label)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_ren_ty_ty {k : nat} {l_label l_ty : nat} {m_label m_ty : nat}
  (sigma : fin k -> ty l_label l_ty)
  (zeta_label : fin l_label -> fin m_label) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_label zeta_ty) sigma x = theta x) :
  forall x,
  funcomp (ren_ty (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty))
    (up_ty_ty sigma) x =
  up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_ty id shift (upRen_ty_label zeta_label)
                (upRen_ty_ty zeta_ty) (funcomp id zeta_label)
                (funcomp shift zeta_ty) (fun x => eq_refl) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_ty zeta_label zeta_ty id shift
                      (funcomp id zeta_label) (funcomp shift zeta_ty)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_ty id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_label_ty {p : nat} {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (zeta_label : fin l_label -> fin m_label) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_label zeta_ty) sigma x = theta x) :
  forall x,
  funcomp
    (ren_ty (upRen_list_label_label p zeta_label)
       (upRen_list_label_ty p zeta_ty))
    (up_list_label_ty p sigma) x =
  up_list_label_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ty (shift_p p) id (upRen_list_label_label p zeta_label)
            (upRen_list_label_ty p zeta_ty) (funcomp (shift_p p) zeta_label)
            (funcomp id zeta_ty) (fun x => scons_p_tail' _ _ x)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ty zeta_label zeta_ty (shift_p p) id
                  (funcomp (shift_p p) zeta_label) (funcomp id zeta_ty)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_ty (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_ty_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (zeta_label : fin l_label -> fin m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (ren_label zeta_label) sigma x = theta x) :
  forall x,
  funcomp (ren_label (upRen_list_ty_label p zeta_label))
    (up_list_ty_label p sigma) x =
  up_list_ty_label p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_label id (upRen_list_ty_label p zeta_label)
            (funcomp id zeta_label) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_label zeta_label id (funcomp id zeta_label)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_ren_list_ty_ty {p : nat} {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (zeta_label : fin l_label -> fin m_label) (zeta_ty : fin l_ty -> fin m_ty)
  (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (ren_ty zeta_label zeta_ty) sigma x = theta x) :
  forall x,
  funcomp
    (ren_ty (upRen_list_ty_label p zeta_label) (upRen_list_ty_ty p zeta_ty))
    (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var_ty m_label (plus p m_ty)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_ty id (shift_p p)
                  (upRen_list_ty_label p zeta_label)
                  (upRen_list_ty_ty p zeta_ty) (funcomp id zeta_label)
                  (funcomp (shift_p p) zeta_ty) (fun x => eq_refl)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_ty zeta_label zeta_ty id (shift_p p)
                        (funcomp id zeta_label) (funcomp (shift_p p) zeta_ty)
                        (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
                  (ap (ren_ty id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_ty {k_label k_ty : nat} {l_label l_ty : nat}
{m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
(sigma_ty : fin m_ty -> ty k_label k_ty)
(zeta_label : fin k_label -> fin l_label) (zeta_ty : fin k_ty -> fin l_ty)
(theta_label : fin m_label -> label l_label)
(theta_ty : fin m_ty -> ty l_label l_ty)
(Eq_label : forall x,
            funcomp (ren_label zeta_label) sigma_label x = theta_label x)
(Eq_ty : forall x,
         funcomp (ren_ty zeta_label zeta_ty) sigma_ty x = theta_ty x)
(s : ty m_label m_ty) {struct s} :
ren_ty zeta_label zeta_ty (subst_ty sigma_label sigma_ty s) =
subst_ty theta_label theta_ty s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 =>
      congr_Data
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstRen_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_subst_ren_ty_label _ _ _ Eq_label)
           (up_subst_ren_ty_ty _ _ _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstRen_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (upRen_ty_label zeta_label) (upRen_ty_ty zeta_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_subst_ren_ty_label _ _ _ Eq_label)
           (up_subst_ren_ty_ty _ _ _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0)
        (compSubstRen_label sigma_label zeta_label theta_label Eq_label s1)
        (compSubstRen_ty (up_label_label sigma_label) (up_label_ty sigma_ty)
           (upRen_label_label zeta_label) (upRen_label_ty zeta_ty)
           (up_label_label theta_label) (up_label_ty theta_ty)
           (up_subst_ren_label_label _ _ _ Eq_label)
           (up_subst_ren_label_ty _ _ _ _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if
        (compSubstRen_constr sigma_label zeta_label theta_label Eq_label s0)
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s1)
        (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty theta_label
           theta_ty Eq_label Eq_ty s2)
  end.

Lemma up_subst_subst_label_ty {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (tau_label : fin l_label -> label m_label)
  (tau_ty : fin l_ty -> ty m_label m_ty) (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (subst_ty tau_label tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_label_label tau_label) (up_label_ty tau_ty))
    (up_label_ty sigma) x =
  up_label_ty theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty shift id (up_label_label tau_label)
            (up_label_ty tau_ty) (funcomp (up_label_label tau_label) shift)
            (funcomp (up_label_ty tau_ty) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_label tau_ty shift id
                  (funcomp (ren_label shift) tau_label)
                  (funcomp (ren_ty shift id) tau_ty) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_ty shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_ty_label {k : nat} {l_label : nat} {m_label : nat}
  (sigma : fin k -> label l_label) (tau_label : fin l_label -> label m_label)
  (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_ty_label tau_label)) (up_ty_label sigma) x =
  up_ty_label theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_label id (up_ty_label tau_label)
            (funcomp (up_ty_label tau_label) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_label tau_label id
                  (funcomp (ren_label id) tau_label) (fun x => eq_refl)
                  (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_subst_ty_ty {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (tau_label : fin l_label -> label m_label)
  (tau_ty : fin l_ty -> ty m_label m_ty) (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (subst_ty tau_label tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_ty_label tau_label) (up_ty_ty tau_ty))
    (up_ty_ty sigma) x =
  up_ty_ty theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_ty id shift (up_ty_label tau_label)
                (up_ty_ty tau_ty) (funcomp (up_ty_label tau_label) id)
                (funcomp (up_ty_ty tau_ty) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_ty tau_label tau_ty id shift
                      (funcomp (ren_label id) tau_label)
                      (funcomp (ren_ty id shift) tau_ty) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_ty id shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_label_ty {p : nat} {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (tau_label : fin l_label -> label m_label)
  (tau_ty : fin l_ty -> ty m_label m_ty) (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (subst_ty tau_label tau_ty) sigma x = theta x) :
  forall x,
  funcomp
    (subst_ty (up_list_label_label p tau_label) (up_list_label_ty p tau_ty))
    (up_list_label_ty p sigma) x =
  up_list_label_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ty (shift_p p) id (up_list_label_label p tau_label)
            (up_list_label_ty p tau_ty)
            (funcomp (up_list_label_label p tau_label) (shift_p p))
            (funcomp (up_list_label_ty p tau_ty) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ty tau_label tau_ty (shift_p p) id _ _
                  (fun x => eq_sym (scons_p_tail' _ _ x))
                  (fun x => eq_sym eq_refl) (sigma n)))
            (ap (ren_ty (shift_p p) id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_ty_label {p : nat} {k : nat} {l_label : nat}
  {m_label : nat} (sigma : fin k -> label l_label)
  (tau_label : fin l_label -> label m_label) (theta : fin k -> label m_label)
  (Eq : forall x, funcomp (subst_label tau_label) sigma x = theta x) :
  forall x,
  funcomp (subst_label (up_list_ty_label p tau_label))
    (up_list_ty_label p sigma) x =
  up_list_ty_label p theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_label id (up_list_ty_label p tau_label)
            (funcomp (up_list_ty_label p tau_label) id) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_label tau_label id _ (fun x => eq_sym eq_refl)
                  (sigma n)))
            (ap (ren_label id) (Eq n)))).
Qed.

Lemma up_subst_subst_list_ty_ty {p : nat} {k : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma : fin k -> ty l_label l_ty)
  (tau_label : fin l_label -> label m_label)
  (tau_ty : fin l_ty -> ty m_label m_ty) (theta : fin k -> ty m_label m_ty)
  (Eq : forall x, funcomp (subst_ty tau_label tau_ty) sigma x = theta x) :
  forall x,
  funcomp (subst_ty (up_list_ty_label p tau_label) (up_list_ty_ty p tau_ty))
    (up_list_ty_ty p sigma) x =
  up_list_ty_ty p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var_ty l_label (plus p l_ty)) (zero_p p)) _
            _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_ty id (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_ty id (shift_p p) (up_list_ty_label p tau_label)
                  (up_list_ty_ty p tau_ty)
                  (funcomp (up_list_ty_label p tau_label) id)
                  (funcomp (up_list_ty_ty p tau_ty) (shift_p p))
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_ty tau_label tau_ty id (shift_p p) _ _
                        (fun x => eq_sym eq_refl)
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_ty id (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_ty {k_label k_ty : nat} {l_label l_ty : nat}
{m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
(sigma_ty : fin m_ty -> ty k_label k_ty)
(tau_label : fin k_label -> label l_label)
(tau_ty : fin k_ty -> ty l_label l_ty)
(theta_label : fin m_label -> label l_label)
(theta_ty : fin m_ty -> ty l_label l_ty)
(Eq_label : forall x,
            funcomp (subst_label tau_label) sigma_label x = theta_label x)
(Eq_ty : forall x,
         funcomp (subst_ty tau_label tau_ty) sigma_ty x = theta_ty x)
(s : ty m_label m_ty) {struct s} :
subst_ty tau_label tau_ty (subst_ty sigma_label sigma_ty s) =
subst_ty theta_label theta_ty s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 =>
      congr_Data
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstSubst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_subst_subst_ty_label _ _ _ Eq_label)
           (up_subst_subst_ty_ty _ _ _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s0)
        (compSubstSubst_ty (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (up_ty_label tau_label) (up_ty_ty tau_ty)
           (up_ty_label theta_label) (up_ty_ty theta_ty)
           (up_subst_subst_ty_label _ _ _ Eq_label)
           (up_subst_subst_ty_ty _ _ _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0)
        (compSubstSubst_label sigma_label tau_label theta_label Eq_label s1)
        (compSubstSubst_ty (up_label_label sigma_label)
           (up_label_ty sigma_ty) (up_label_label tau_label)
           (up_label_ty tau_ty) (up_label_label theta_label)
           (up_label_ty theta_ty) (up_subst_subst_label_label _ _ _ Eq_label)
           (up_subst_subst_label_ty _ _ _ _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if
        (compSubstSubst_constr sigma_label tau_label theta_label Eq_label s0)
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s1)
        (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty theta_label
           theta_ty Eq_label Eq_ty s2)
  end.

Lemma renRen_ty {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
  (xi_ty : fin m_ty -> fin k_ty) (zeta_label : fin k_label -> fin l_label)
  (zeta_ty : fin k_ty -> fin l_ty) (s : ty m_label m_ty) :
  ren_ty zeta_label zeta_ty (ren_ty xi_label xi_ty s) =
  ren_ty (funcomp zeta_label xi_label) (funcomp zeta_ty xi_ty) s.
Proof.
exact (compRenRen_ty xi_label xi_ty zeta_label zeta_ty _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_ty_pointwise {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
  (xi_ty : fin m_ty -> fin k_ty) (zeta_label : fin k_label -> fin l_label)
  (zeta_ty : fin k_ty -> fin l_ty) :
  pointwise_relation _ eq
    (funcomp (ren_ty zeta_label zeta_ty) (ren_ty xi_label xi_ty))
    (ren_ty (funcomp zeta_label xi_label) (funcomp zeta_ty xi_ty)).
Proof.
exact (fun s =>
       compRenRen_ty xi_label xi_ty zeta_label zeta_ty _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
  (xi_ty : fin m_ty -> fin k_ty) (tau_label : fin k_label -> label l_label)
  (tau_ty : fin k_ty -> ty l_label l_ty) (s : ty m_label m_ty) :
  subst_ty tau_label tau_ty (ren_ty xi_label xi_ty s) =
  subst_ty (funcomp tau_label xi_label) (funcomp tau_ty xi_ty) s.
Proof.
exact (compRenSubst_ty xi_label xi_ty tau_label tau_ty _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_ty_pointwise {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (xi_label : fin m_label -> fin k_label)
  (xi_ty : fin m_ty -> fin k_ty) (tau_label : fin k_label -> label l_label)
  (tau_ty : fin k_ty -> ty l_label l_ty) :
  pointwise_relation _ eq
    (funcomp (subst_ty tau_label tau_ty) (ren_ty xi_label xi_ty))
    (subst_ty (funcomp tau_label xi_label) (funcomp tau_ty xi_ty)).
Proof.
exact (fun s =>
       compRenSubst_ty xi_label xi_ty tau_label tau_ty _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_ty {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_ty : fin m_ty -> ty k_label k_ty)
  (zeta_label : fin k_label -> fin l_label) (zeta_ty : fin k_ty -> fin l_ty)
  (s : ty m_label m_ty) :
  ren_ty zeta_label zeta_ty (subst_ty sigma_label sigma_ty s) =
  subst_ty (funcomp (ren_label zeta_label) sigma_label)
    (funcomp (ren_ty zeta_label zeta_ty) sigma_ty) s.
Proof.
exact (compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_ty_pointwise {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_ty : fin m_ty -> ty k_label k_ty)
  (zeta_label : fin k_label -> fin l_label) (zeta_ty : fin k_ty -> fin l_ty)
  :
  pointwise_relation _ eq
    (funcomp (ren_ty zeta_label zeta_ty) (subst_ty sigma_label sigma_ty))
    (subst_ty (funcomp (ren_label zeta_label) sigma_label)
       (funcomp (ren_ty zeta_label zeta_ty) sigma_ty)).
Proof.
exact (fun s =>
       compSubstRen_ty sigma_label sigma_ty zeta_label zeta_ty _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_ty : fin m_ty -> ty k_label k_ty)
  (tau_label : fin k_label -> label l_label)
  (tau_ty : fin k_ty -> ty l_label l_ty) (s : ty m_label m_ty) :
  subst_ty tau_label tau_ty (subst_ty sigma_label sigma_ty s) =
  subst_ty (funcomp (subst_label tau_label) sigma_label)
    (funcomp (subst_ty tau_label tau_ty) sigma_ty) s.
Proof.
exact (compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_ty_pointwise {k_label k_ty : nat} {l_label l_ty : nat}
  {m_label m_ty : nat} (sigma_label : fin m_label -> label k_label)
  (sigma_ty : fin m_ty -> ty k_label k_ty)
  (tau_label : fin k_label -> label l_label)
  (tau_ty : fin k_ty -> ty l_label l_ty) :
  pointwise_relation _ eq
    (funcomp (subst_ty tau_label tau_ty) (subst_ty sigma_label sigma_ty))
    (subst_ty (funcomp (subst_label tau_label) sigma_label)
       (funcomp (subst_ty tau_label tau_ty) sigma_ty)).
Proof.
exact (fun s =>
       compSubstSubst_ty sigma_label sigma_ty tau_label tau_ty _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_label_ty {m : nat} {n_label n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_label n_ty)
  (Eq : forall x, funcomp (var_ty n_label n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty (S n_label) n_ty) (upRen_label_ty xi) x =
  up_label_ty sigma x.
Proof.
exact (fun n => ap (ren_ty shift id) (Eq n)).
Qed.

Lemma rinstInst_up_ty_label {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label n_label) (upRen_ty_label xi) x = up_ty_label sigma x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma rinstInst_up_ty_ty {m : nat} {n_label n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_label n_ty)
  (Eq : forall x, funcomp (var_ty n_label n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty n_label (S n_ty)) (upRen_ty_ty xi) x = up_ty_ty sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_ty id shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_label_ty {p : nat} {m : nat} {n_label n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_label n_ty)
  (Eq : forall x, funcomp (var_ty n_label n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty (plus p n_label) n_ty) (upRen_list_label_ty p xi) x =
  up_list_label_ty p sigma x.
Proof.
exact (fun n => ap (ren_ty (shift_p p) id) (Eq n)).
Qed.

Lemma rinstInst_up_list_ty_label {p : nat} {m : nat} {n_label : nat}
  (xi : fin m -> fin n_label) (sigma : fin m -> label n_label)
  (Eq : forall x, funcomp (var_label n_label) xi x = sigma x) :
  forall x,
  funcomp (var_label n_label) (upRen_list_ty_label p xi) x =
  up_list_ty_label p sigma x.
Proof.
exact (fun n => ap (ren_label id) (Eq n)).
Qed.

Lemma rinstInst_up_list_ty_ty {p : nat} {m : nat} {n_label n_ty : nat}
  (xi : fin m -> fin n_ty) (sigma : fin m -> ty n_label n_ty)
  (Eq : forall x, funcomp (var_ty n_label n_ty) xi x = sigma x) :
  forall x,
  funcomp (var_ty n_label (plus p n_ty)) (upRen_list_ty_ty p xi) x =
  up_list_ty_ty p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var_ty n_label (plus p n_ty)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_ty id (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_ty {m_label m_ty : nat} {n_label n_ty : nat}
(xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty)
(sigma_label : fin m_label -> label n_label)
(sigma_ty : fin m_ty -> ty n_label n_ty)
(Eq_label : forall x, funcomp (var_label n_label) xi_label x = sigma_label x)
(Eq_ty : forall x, funcomp (var_ty n_label n_ty) xi_ty x = sigma_ty x)
(s : ty m_label m_ty) {struct s} :
ren_ty xi_label xi_ty s = subst_ty sigma_label sigma_ty s :=
  match s with
  | var_ty _ _ s0 => Eq_ty s0
  | Any _ _ => congr_Any
  | Unit _ _ => congr_Unit
  | Data _ _ s0 =>
      congr_Data (rinst_inst_label xi_label sigma_label Eq_label s0)
  | Ref _ _ s0 =>
      congr_Ref
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
  | arr _ _ s0 s1 =>
      congr_arr
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | prod _ _ s0 s1 =>
      congr_prod
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | sum _ _ s0 s1 =>
      congr_sum
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s1)
  | all _ _ s0 s1 =>
      congr_all
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (rinst_inst_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_label _ _ Eq_label)
           (rinstInst_up_ty_ty _ _ Eq_ty) s1)
  | ex _ _ s0 s1 =>
      congr_ex
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s0)
        (rinst_inst_ty (upRen_ty_label xi_label) (upRen_ty_ty xi_ty)
           (up_ty_label sigma_label) (up_ty_ty sigma_ty)
           (rinstInst_up_ty_label _ _ Eq_label)
           (rinstInst_up_ty_ty _ _ Eq_ty) s1)
  | all_l _ _ s0 s1 s2 =>
      congr_all_l (eq_refl s0)
        (rinst_inst_label xi_label sigma_label Eq_label s1)
        (rinst_inst_ty (upRen_label_label xi_label) (upRen_label_ty xi_ty)
           (up_label_label sigma_label) (up_label_ty sigma_ty)
           (rinstInst_up_label_label _ _ Eq_label)
           (rinstInst_up_label_ty _ _ Eq_ty) s2)
  | t_if _ _ s0 s1 s2 =>
      congr_t_if (rinst_inst_constr xi_label sigma_label Eq_label s0)
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s1)
        (rinst_inst_ty xi_label xi_ty sigma_label sigma_ty Eq_label Eq_ty s2)
  end.

Lemma rinstInst'_ty {m_label m_ty : nat} {n_label n_ty : nat}
  (xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty)
  (s : ty m_label m_ty) :
  ren_ty xi_label xi_ty s =
  subst_ty (funcomp (var_label n_label) xi_label)
    (funcomp (var_ty n_label n_ty) xi_ty) s.
Proof.
exact (rinst_inst_ty xi_label xi_ty _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstInst'_ty_pointwise {m_label m_ty : nat} {n_label n_ty : nat}
  (xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty) :
  pointwise_relation _ eq (ren_ty xi_label xi_ty)
    (subst_ty (funcomp (var_label n_label) xi_label)
       (funcomp (var_ty n_label n_ty) xi_ty)).
Proof.
exact (fun s =>
       rinst_inst_ty xi_label xi_ty _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma instId'_ty {m_label m_ty : nat} (s : ty m_label m_ty) :
  subst_ty (var_label m_label) (var_ty m_label m_ty) s = s.
Proof.
exact (idSubst_ty (var_label m_label) (var_ty m_label m_ty)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_ty_pointwise {m_label m_ty : nat} :
  pointwise_relation _ eq
    (subst_ty (var_label m_label) (var_ty m_label m_ty)) id.
Proof.
exact (fun s =>
       idSubst_ty (var_label m_label) (var_ty m_label m_ty)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ty {m_label m_ty : nat} (s : ty m_label m_ty) :
  ren_ty id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id id s)).
Qed.

Lemma rinstId'_ty_pointwise {m_label m_ty : nat} :
  pointwise_relation _ eq (@ren_ty m_label m_ty m_label m_ty id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_ty s) (rinstInst'_ty id id s)).
Qed.

Lemma varL'_ty {m_label m_ty : nat} {n_label n_ty : nat}
  (sigma_label : fin m_label -> label n_label)
  (sigma_ty : fin m_ty -> ty n_label n_ty) (x : fin m_ty) :
  subst_ty sigma_label sigma_ty (var_ty m_label m_ty x) = sigma_ty x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ty_pointwise {m_label m_ty : nat} {n_label n_ty : nat}
  (sigma_label : fin m_label -> label n_label)
  (sigma_ty : fin m_ty -> ty n_label n_ty) :
  pointwise_relation _ eq
    (funcomp (subst_ty sigma_label sigma_ty) (var_ty m_label m_ty)) sigma_ty.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_ty {m_label m_ty : nat} {n_label n_ty : nat}
  (xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty)
  (x : fin m_ty) :
  ren_ty xi_label xi_ty (var_ty m_label m_ty x) =
  var_ty n_label n_ty (xi_ty x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ty_pointwise {m_label m_ty : nat} {n_label n_ty : nat}
  (xi_label : fin m_label -> fin n_label) (xi_ty : fin m_ty -> fin n_ty) :
  pointwise_relation _ eq
    (funcomp (ren_ty xi_label xi_ty) (var_ty m_label m_ty))
    (funcomp (var_ty n_label n_ty) xi_ty).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_ty X Y :=
    up_ty : X -> Y.

Class Up_tm X Y :=
    up_tm : X -> Y.

Class Up_constr X Y :=
    up_constr : X -> Y.

Class Up_label X Y :=
    up_label : X -> Y.

#[global]
Instance Subst_ty  {m_label m_ty n_label n_ty : nat}: (Subst2 _ _ _ _) :=
 (@subst_ty m_label m_ty n_label n_ty).

#[global]
Instance Up_ty_ty  {m n_label n_ty : nat}: (Up_ty _ _) :=
 (@up_ty_ty m n_label n_ty).

#[global]
Instance Up_ty_label  {m n_label : nat}: (Up_label _ _) :=
 (@up_ty_label m n_label).

#[global]
Instance Up_label_ty  {m n_label n_ty : nat}: (Up_ty _ _) :=
 (@up_label_ty m n_label n_ty).

#[global]
Instance Ren_ty  {m_label m_ty n_label n_ty : nat}: (Ren2 _ _ _ _) :=
 (@ren_ty m_label m_ty n_label n_ty).

#[global]
Instance VarInstance_ty  {n_label n_ty : nat}: (Var _ _) :=
 (@var_ty n_label n_ty).

#[global]
Instance Subst_tm  {m_label m_tm n_label n_tm : nat}: (Subst2 _ _ _ _) :=
 (@subst_tm m_label m_tm n_label n_tm).

#[global]
Instance Up_tm_tm  {m n_label n_tm : nat}: (Up_tm _ _) :=
 (@up_tm_tm m n_label n_tm).

#[global]
Instance Up_tm_label  {m n_label : nat}: (Up_label _ _) :=
 (@up_tm_label m n_label).

#[global]
Instance Up_label_tm  {m n_label n_tm : nat}: (Up_tm _ _) :=
 (@up_label_tm m n_label n_tm).

#[global]
Instance Ren_tm  {m_label m_tm n_label n_tm : nat}: (Ren2 _ _ _ _) :=
 (@ren_tm m_label m_tm n_label n_tm).

#[global]
Instance VarInstance_tm  {n_label n_tm : nat}: (Var _ _) :=
 (@var_tm n_label n_tm).

#[global]
Instance Subst_constr  {m_label n_label : nat}: (Subst1 _ _ _) :=
 (@subst_constr m_label n_label).

#[global]
Instance Ren_constr  {m_label n_label : nat}: (Ren1 _ _ _) :=
 (@ren_constr m_label n_label).

#[global]
Instance Subst_label  {m_label n_label : nat}: (Subst1 _ _ _) :=
 (@subst_label m_label n_label).

#[global]
Instance Up_label_label  {m n_label : nat}: (Up_label _ _) :=
 (@up_label_label m n_label).

#[global]
Instance Ren_label  {m_label n_label : nat}: (Ren1 _ _ _) :=
 (@ren_label m_label n_label).

#[global]
Instance VarInstance_label  {n_label : nat}: (Var _ _) :=
 (@var_label n_label).

Notation "s [ sigma_label ; sigma_ty ]" := (subst_ty sigma_label sigma_ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ty" := up_ty (only printing)  : subst_scope.

Notation "↑__ty" := up_ty_ty (only printing)  : subst_scope.

Notation "↑__label" := up_ty_label (only printing)  : subst_scope.

Notation "↑__ty" := up_label_ty (only printing)  : subst_scope.

Notation "s ⟨ xi_label ; xi_ty ⟩" := (ren_ty xi_label xi_ty s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_ty ( at level 1, only printing)  : subst_scope.

Notation "x '__ty'" := (@ids _ _ VarInstance_ty x)
( at level 5, format "x __ty", only printing)  : subst_scope.

Notation "x '__ty'" := (var_ty x) ( at level 5, format "x __ty")  :
subst_scope.

Notation "s [ sigma_label ; sigma_tm ]" := (subst_tm sigma_label sigma_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__tm" := up_tm (only printing)  : subst_scope.

Notation "↑__tm" := up_tm_tm (only printing)  : subst_scope.

Notation "↑__label" := up_tm_label (only printing)  : subst_scope.

Notation "↑__tm" := up_label_tm (only printing)  : subst_scope.

Notation "s ⟨ xi_label ; xi_tm ⟩" := (ren_tm xi_label xi_tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_tm ( at level 1, only printing)  : subst_scope.

Notation "x '__tm'" := (@ids _ _ VarInstance_tm x)
( at level 5, format "x __tm", only printing)  : subst_scope.

Notation "x '__tm'" := (var_tm x) ( at level 5, format "x __tm")  :
subst_scope.

Notation "s [ sigma_label ]" := (subst_constr sigma_label s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__constr" := up_constr (only printing)  : subst_scope.

Notation "s ⟨ xi_label ⟩" := (ren_constr xi_label s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s [ sigma_label ]" := (subst_label sigma_label s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__label" := up_label (only printing)  : subst_scope.

Notation "↑__label" := up_label_label (only printing)  : subst_scope.

Notation "s ⟨ xi_label ⟩" := (ren_label xi_label s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_label ( at level 1, only printing)  : subst_scope.

Notation "x '__label'" := (@ids _ _ VarInstance_label x)
( at level 5, format "x __label", only printing)  : subst_scope.

Notation "x '__label'" := (var_label x) ( at level 5, format "x __label")  :
subst_scope.

#[global]
Instance subst_ty_morphism  {m_label m_ty : nat} {n_label n_ty : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_ty m_label m_ty n_label n_ty)).
Proof.
exact (fun f_label g_label Eq_label f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s
         (fun t' => subst_ty f_label f_ty s = subst_ty g_label g_ty t')
         (ext_ty f_label f_ty g_label g_ty Eq_label Eq_ty s) t Eq_st).
Qed.

#[global]
Instance subst_ty_morphism2  {m_label m_ty : nat} {n_label n_ty : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_ty m_label m_ty n_label n_ty)).
Proof.
exact (fun f_label g_label Eq_label f_ty g_ty Eq_ty s =>
       ext_ty f_label f_ty g_label g_ty Eq_label Eq_ty s).
Qed.

#[global]
Instance ren_ty_morphism  {m_label m_ty : nat} {n_label n_ty : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_ty m_label m_ty n_label n_ty)).
Proof.
exact (fun f_label g_label Eq_label f_ty g_ty Eq_ty s t Eq_st =>
       eq_ind s (fun t' => ren_ty f_label f_ty s = ren_ty g_label g_ty t')
         (extRen_ty f_label f_ty g_label g_ty Eq_label Eq_ty s) t Eq_st).
Qed.

#[global]
Instance ren_ty_morphism2  {m_label m_ty : nat} {n_label n_ty : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_ty m_label m_ty n_label n_ty)).
Proof.
exact (fun f_label g_label Eq_label f_ty g_ty Eq_ty s =>
       extRen_ty f_label f_ty g_label g_ty Eq_label Eq_ty s).
Qed.

#[global]
Instance subst_tm_morphism  {m_label m_tm : nat} {n_label n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_tm m_label m_tm n_label n_tm)).
Proof.
exact (fun f_label g_label Eq_label f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s
         (fun t' => subst_tm f_label f_tm s = subst_tm g_label g_tm t')
         (ext_tm f_label f_tm g_label g_tm Eq_label Eq_tm s) t Eq_st).
Qed.

#[global]
Instance subst_tm_morphism2  {m_label m_tm : nat} {n_label n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_tm m_label m_tm n_label n_tm)).
Proof.
exact (fun f_label g_label Eq_label f_tm g_tm Eq_tm s =>
       ext_tm f_label f_tm g_label g_tm Eq_label Eq_tm s).
Qed.

#[global]
Instance ren_tm_morphism  {m_label m_tm : nat} {n_label n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@ren_tm m_label m_tm n_label n_tm)).
Proof.
exact (fun f_label g_label Eq_label f_tm g_tm Eq_tm s t Eq_st =>
       eq_ind s (fun t' => ren_tm f_label f_tm s = ren_tm g_label g_tm t')
         (extRen_tm f_label f_tm g_label g_tm Eq_label Eq_tm s) t Eq_st).
Qed.

#[global]
Instance ren_tm_morphism2  {m_label m_tm : nat} {n_label n_tm : nat}:
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_tm m_label m_tm n_label n_tm)).
Proof.
exact (fun f_label g_label Eq_label f_tm g_tm Eq_tm s =>
       extRen_tm f_label f_tm g_label g_tm Eq_label Eq_tm s).
Qed.

#[global]
Instance subst_constr_morphism  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_constr m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s t Eq_st =>
       eq_ind s (fun t' => subst_constr f_label s = subst_constr g_label t')
         (ext_constr f_label g_label Eq_label s) t Eq_st).
Qed.

#[global]
Instance subst_constr_morphism2  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_constr m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s =>
       ext_constr f_label g_label Eq_label s).
Qed.

#[global]
Instance ren_constr_morphism  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_constr m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s t Eq_st =>
       eq_ind s (fun t' => ren_constr f_label s = ren_constr g_label t')
         (extRen_constr f_label g_label Eq_label s) t Eq_st).
Qed.

#[global]
Instance ren_constr_morphism2  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_constr m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s =>
       extRen_constr f_label g_label Eq_label s).
Qed.

#[global]
Instance subst_label_morphism  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_label m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s t Eq_st =>
       eq_ind s (fun t' => subst_label f_label s = subst_label g_label t')
         (ext_label f_label g_label Eq_label s) t Eq_st).
Qed.

#[global]
Instance subst_label_morphism2  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_label m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s => ext_label f_label g_label Eq_label s).
Qed.

#[global]
Instance ren_label_morphism  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_label m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s t Eq_st =>
       eq_ind s (fun t' => ren_label f_label s = ren_label g_label t')
         (extRen_label f_label g_label Eq_label s) t Eq_st).
Qed.

#[global]
Instance ren_label_morphism2  {m_label : nat} {n_label : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_label m_label n_label)).
Proof.
exact (fun f_label g_label Eq_label s =>
       extRen_label f_label g_label Eq_label s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_label, Var, ids, Ren_label, Ren1,
                      ren1, Up_label_label, Up_label, up_label, Subst_label,
                      Subst1, subst1, Ren_constr, Ren1, ren1, Subst_constr,
                      Subst1, subst1, VarInstance_tm, Var, ids, Ren_tm, Ren2,
                      ren2, Up_label_tm, Up_tm, up_tm, Up_tm_label, Up_label,
                      up_label, Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst2,
                      subst2, VarInstance_ty, Var, ids, Ren_ty, Ren2, ren2,
                      Up_label_ty, Up_ty, up_ty, Up_ty_label, Up_label,
                      up_label, Up_ty_ty, Up_ty, up_ty, Subst_ty, Subst2,
                      subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_label, Var,
                                            ids, Ren_label, Ren1, ren1,
                                            Up_label_label, Up_label,
                                            up_label, Subst_label, Subst1,
                                            subst1, Ren_constr, Ren1, ren1,
                                            Subst_constr, Subst1, subst1,
                                            VarInstance_tm, Var, ids, Ren_tm,
                                            Ren2, ren2, Up_label_tm, Up_tm,
                                            up_tm, Up_tm_label, Up_label,
                                            up_label, Up_tm_tm, Up_tm, up_tm,
                                            Subst_tm, Subst2, subst2,
                                            VarInstance_ty, Var, ids, Ren_ty,
                                            Ren2, ren2, Up_label_ty, Up_ty,
                                            up_ty, Up_ty_label, Up_label,
                                            up_label, Up_ty_ty, Up_ty, up_ty,
                                            Subst_ty, Subst2, subst2 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_ty_pointwise
                 | progress setoid_rewrite substSubst_ty
                 | progress setoid_rewrite substRen_ty_pointwise
                 | progress setoid_rewrite substRen_ty
                 | progress setoid_rewrite renSubst_ty_pointwise
                 | progress setoid_rewrite renSubst_ty
                 | progress setoid_rewrite renRen'_ty_pointwise
                 | progress setoid_rewrite renRen_ty
                 | progress setoid_rewrite substSubst_tm_pointwise
                 | progress setoid_rewrite substSubst_tm
                 | progress setoid_rewrite substRen_tm_pointwise
                 | progress setoid_rewrite substRen_tm
                 | progress setoid_rewrite renSubst_tm_pointwise
                 | progress setoid_rewrite renSubst_tm
                 | progress setoid_rewrite renRen'_tm_pointwise
                 | progress setoid_rewrite renRen_tm
                 | progress setoid_rewrite substSubst_constr_pointwise
                 | progress setoid_rewrite substSubst_constr
                 | progress setoid_rewrite substRen_constr_pointwise
                 | progress setoid_rewrite substRen_constr
                 | progress setoid_rewrite renSubst_constr_pointwise
                 | progress setoid_rewrite renSubst_constr
                 | progress setoid_rewrite renRen'_constr_pointwise
                 | progress setoid_rewrite renRen_constr
                 | progress setoid_rewrite substSubst_label_pointwise
                 | progress setoid_rewrite substSubst_label
                 | progress setoid_rewrite substRen_label_pointwise
                 | progress setoid_rewrite substRen_label
                 | progress setoid_rewrite renSubst_label_pointwise
                 | progress setoid_rewrite renSubst_label
                 | progress setoid_rewrite renRen'_label_pointwise
                 | progress setoid_rewrite renRen_label
                 | progress setoid_rewrite varLRen'_ty_pointwise
                 | progress setoid_rewrite varLRen'_ty
                 | progress setoid_rewrite varL'_ty_pointwise
                 | progress setoid_rewrite varL'_ty
                 | progress setoid_rewrite rinstId'_ty_pointwise
                 | progress setoid_rewrite rinstId'_ty
                 | progress setoid_rewrite instId'_ty_pointwise
                 | progress setoid_rewrite instId'_ty
                 | progress setoid_rewrite varLRen'_tm_pointwise
                 | progress setoid_rewrite varLRen'_tm
                 | progress setoid_rewrite varL'_tm_pointwise
                 | progress setoid_rewrite varL'_tm
                 | progress setoid_rewrite rinstId'_tm_pointwise
                 | progress setoid_rewrite rinstId'_tm
                 | progress setoid_rewrite instId'_tm_pointwise
                 | progress setoid_rewrite instId'_tm
                 | progress setoid_rewrite rinstId'_constr_pointwise
                 | progress setoid_rewrite rinstId'_constr
                 | progress setoid_rewrite instId'_constr_pointwise
                 | progress setoid_rewrite instId'_constr
                 | progress setoid_rewrite varLRen'_label_pointwise
                 | progress setoid_rewrite varLRen'_label
                 | progress setoid_rewrite varL'_label_pointwise
                 | progress setoid_rewrite varL'_label
                 | progress setoid_rewrite rinstId'_label_pointwise
                 | progress setoid_rewrite rinstId'_label
                 | progress setoid_rewrite instId'_label_pointwise
                 | progress setoid_rewrite instId'_label
                 | progress
                    unfold up_list_ty_ty, up_list_ty_label, up_list_label_ty,
                     up_ty_ty, up_ty_label, up_label_ty, upRen_list_ty_ty,
                     upRen_list_ty_label, upRen_list_label_ty, upRen_ty_ty,
                     upRen_ty_label, upRen_label_ty, up_list_tm_tm,
                     up_list_tm_label, up_list_label_tm, up_tm_tm,
                     up_tm_label, up_label_tm, upRen_list_tm_tm,
                     upRen_list_tm_label, upRen_list_label_tm, upRen_tm_tm,
                     upRen_tm_label, upRen_label_tm, up_list_label_label,
                     up_label_label, upRen_list_label_label,
                     upRen_label_label, up_ren
                 | progress
                    cbn[subst_ty ren_ty subst_tm ren_tm subst_constr
                       ren_constr subst_label ren_label]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_label, Var, ids, Ren_label, Ren1, ren1,
                  Up_label_label, Up_label, up_label, Subst_label, Subst1,
                  subst1, Ren_constr, Ren1, ren1, Subst_constr, Subst1,
                  subst1, VarInstance_tm, Var, ids, Ren_tm, Ren2, ren2,
                  Up_label_tm, Up_tm, up_tm, Up_tm_label, Up_label, up_label,
                  Up_tm_tm, Up_tm, up_tm, Subst_tm, Subst2, subst2,
                  VarInstance_ty, Var, ids, Ren_ty, Ren2, ren2, Up_label_ty,
                  Up_ty, up_ty, Up_ty_label, Up_label, up_label, Up_ty_ty,
                  Up_ty, up_ty, Subst_ty, Subst2, subst2 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_ty_pointwise;
                  try setoid_rewrite rinstInst'_ty;
                  try setoid_rewrite rinstInst'_tm_pointwise;
                  try setoid_rewrite rinstInst'_tm;
                  try setoid_rewrite rinstInst'_constr_pointwise;
                  try setoid_rewrite rinstInst'_constr;
                  try setoid_rewrite rinstInst'_label_pointwise;
                  try setoid_rewrite rinstInst'_label.

Ltac renamify := auto_unfold; try setoid_rewrite_left rinstInst'_ty_pointwise;
                  try setoid_rewrite_left rinstInst'_ty;
                  try setoid_rewrite_left rinstInst'_tm_pointwise;
                  try setoid_rewrite_left rinstInst'_tm;
                  try setoid_rewrite_left rinstInst'_constr_pointwise;
                  try setoid_rewrite_left rinstInst'_constr;
                  try setoid_rewrite_left rinstInst'_label_pointwise;
                  try setoid_rewrite_left rinstInst'_label.

End Core.

Module Extra.

Import
Core.

Arguments var_ty {n_label n_ty}.

Arguments t_if {n_label n_ty}.

Arguments all_l {n_label n_ty}.

Arguments ex {n_label n_ty}.

Arguments all {n_label n_ty}.

Arguments sum {n_label n_ty}.

Arguments prod {n_label n_ty}.

Arguments arr {n_label n_ty}.

Arguments Ref {n_label n_ty}.

Arguments Data {n_label n_ty}.

Arguments Unit {n_label n_ty}.

Arguments Any {n_label n_ty}.

Arguments var_tm {n_label n_tm}.

Arguments sync {n_label n_tm}.

Arguments if_c {n_label n_tm}.

Arguments if_tm {n_label n_tm}.

Arguments unpack {n_label n_tm}.

Arguments pack {n_label n_tm}.

Arguments lapp {n_label n_tm}.

Arguments tapp {n_label n_tm}.

Arguments case {n_label n_tm}.

Arguments inr {n_label n_tm}.

Arguments inl {n_label n_tm}.

Arguments right_tm {n_label n_tm}.

Arguments left_tm {n_label n_tm}.

Arguments tm_pair {n_label n_tm}.

Arguments assign {n_label n_tm}.

Arguments dealloc {n_label n_tm}.

Arguments alloc {n_label n_tm}.

Arguments app {n_label n_tm}.

Arguments zero {n_label n_tm}.

Arguments Op {n_label n_tm}.

Arguments l_lam {n_label n_tm}.

Arguments tlam {n_label n_tm}.

Arguments fixlam {n_label n_tm}.

Arguments loc {n_label n_tm}.

Arguments bitstring {n_label n_tm}.

Arguments skip {n_label n_tm}.

Arguments error {n_label n_tm}.

Arguments condition {n_label}.

Arguments var_label {n_label}.

Arguments lmeet {n_label}.

Arguments ljoin {n_label}.

Arguments latl {n_label}.

#[global] Hint Opaque subst_ty: rewrite.

#[global] Hint Opaque ren_ty: rewrite.

#[global] Hint Opaque subst_tm: rewrite.

#[global] Hint Opaque ren_tm: rewrite.

#[global] Hint Opaque subst_constr: rewrite.

#[global] Hint Opaque ren_constr: rewrite.

#[global] Hint Opaque subst_label: rewrite.

#[global] Hint Opaque ren_label: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

