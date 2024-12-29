Require Import Setoid.
Require Import AbstractSecurity.
  
(* Below are some basic lemmas for the abstract security notions. *)

(* force of map = map of force *)
Lemma force_map {A B} (p : Proc EmptyOracle A) (f : A -> B) : 
  force (mapProc p f) = f (force p).
  destruct p.
  auto.
  destruct q.
Qed.

Hint Rewrite @force_map : sec.

(* force of map = bind of force *)
Lemma force_bind {A B} (p : Proc EmptyOracle A) (f : A -> Proc EmptyOracle B) : 
  force (bind p f) = force (f (force p)).
  destruct p.
  auto.
  destruct q.
Qed.

Hint Rewrite @force_bind : sec.

(* The bisimulation rule for systems.
   To show two systems (with the same set of oracles) are equivalent, it suffices to show a 
   _bisimulation_: an invariant over the two states such that:
   - The initial states are related;
   - Any two related states have equal outputs; and 
   - Given two related states, any identical oracle call against the two systems result in equal responses, and the updated states are still related. *)
Lemma EquivBisim {O} {Out} (S1 S2 : Sys O EmptyOracle Out)
   (R : S1.(state) -> S2.(state) -> Prop) 
   (h1 : forall s1 s2, R s1 s2 -> S1.(output) s1 = S2.(output) s2) 
   (h2 : forall s1 s2, R s1 s2 -> forall q, 
            let '(s1', r1) := force (S1.(run) s1 q) in 
            let '(s2', r2) := force (S2.(run) s2 q) in 
            R s1' s2' /\ r1 = r2) :
   forall s1 s2, 
     R s1 s2 ->
     EquivSys S1 S2 s1 s2.
    intros.
    intro.
    unfold runProcOut.
    autorewrite with sec.
    revert s1 s2 H.
    induction A; intros.
    simpl.
    rewrite (h1 _ _ H); auto.
    simpl.
    autorewrite with sec.
    specialize (h2 _ _ H0 q).
    destruct (force _).
    destruct (force _).
    destruct h2; subst.
    apply H.
    auto.
Qed.


(* The identity or "copycat" system *)
Definition IdSys {O} : Sys O O unit :=
  {| state := unit; 
     run := fun _ q => PQuery q (fun r => PRet (tt, r)); 
     output := fun _ => tt |}.
  
(* Linking with the identity system results is equivalent to not linking with it *)
Lemma LinkSys_IdSys {O} {Out} (S : Sys O EmptyOracle Out) s : 
  EquivSys S (LinkSys IdSys S) s (tt, s).
  apply (EquivBisim S (LinkSys IdSys S) (fun s1 s2 => s1 = snd s2)).
  {
    intros.
    destruct s2; simpl in *; subst.
    auto.
  }
  {
    simpl.
    intros.
    destruct s2; simpl in *; subst.
    autorewrite with sec.
    destruct (force _).
    simpl.
    auto.
  }
  {
    auto.
  }
Qed.


(* Instantiates is Reflexive *)
Lemma InstRefl {O} {Secret} {Out}
    (S1 : Sys O EmptyOracle Out) (st1 : Secret -> S1.(state)) : 
  Instantiates S1 S1 st1 st1.
  (* The simulator is the identity system. *)
  exists IdSys.
  exists tt.
  intro.
  apply LinkSys_IdSys.
Qed.
 
(* EquivSys is transitive *)
Lemma EquivSys_tr {O} {Out} (S1 S2 S3 : Sys O EmptyOracle Out) s1 s2 s3 : 
  EquivSys S1 S2 s1 s2 -> 
  EquivSys S2 S3 s2 s3 -> 
  EquivSys S1 S3 s1 s3.
  intros; intro.
  rewrite H.
  auto.
Qed.

(* EquivSys is symmetric *)
Lemma EquivSys_sym {O} {Out} (S1 S2 : Sys O EmptyOracle Out) s1 s2 : 
  EquivSys S1 S2 s1 s2 -> 
  EquivSys S2 S1 s2 s1.
  intros; intro.
  rewrite H.
  auto.
Qed.

(* EquivSys is reflexive *)
Lemma EquivSys_refl {O} {Out} (S : Sys O EmptyOracle Out) s :
  EquivSys S S s s.
  intro; auto.
Qed.


(* Some basic lemmas about how bind and runProc interact *)
Lemma bind_runProc {O} {Out} {R R'} (S : Sys O EmptyOracle Out) (A : Proc O R) (k : R  * state S -> Proc EmptyOracle R') s : 
  bind (runProc A S s) k = 
  let '(x, y) := force (runProc A S s) in 
  k (x, y).
  destruct (runProc A S s).
  simpl.
  destruct p.
  auto.
  destruct q.
Qed.

Hint Rewrite @bind_runProc : sec.
                 

Lemma map_runProc {O} {Out} {R R'} (S : Sys O EmptyOracle Out) (A : Proc O R) (k : R  * state S -> R') s : 
  mapProc (runProc A S s) k = 
  let '(x, y) := force (runProc A S s) in 
  PRet (k (x, y)).
  unfold mapProc.
  rewrite bind_runProc.
  auto.
Qed.

Hint Rewrite @map_runProc : sec.

Lemma bind_bind {R1 R2 R3} (p : Proc EmptyOracle R1) (k1 : R1 -> Proc EmptyOracle R2) (k2 : R2 -> Proc EmptyOracle R3)  :
  bind (bind p k1) k2 = 
  bind p (fun x => bind (k1 x) k2).
  induction p.
  auto.
  simpl.
  destruct q.
Qed.

Hint Rewrite @bind_bind : sec.

Lemma runProc_bind {O} {Out} {R R'} (S : Sys O EmptyOracle Out) (A : Proc O R) (k : R -> Proc O R') s : 
  runProc (bind A k) S s = 
  bind (runProc A S s) (fun '(x, s') => runProc (k x) S s').
  revert s.
  induction A.
  simpl.
  auto.
  simpl.
  intros.
  autorewrite with sec.
  destruct (run S s q).
  2: {
    destruct q0.
  }
  simpl.
  destruct p0.
  rewrite H.
  auto.
Qed.

Hint Rewrite @runProc_bind : sec.

Lemma runProc_map {O} {Out} {R R'} (S : Sys O EmptyOracle Out) (A : Proc O R) (k : R -> R') s : 
  runProc (mapProc A k) S s = 
  let '(x, s') := force (runProc A S s) in PRet (k x, s'). 
  unfold mapProc.
  rewrite runProc_bind.
  destruct (runProc A S s).
  auto.
  destruct q.
Qed.

Hint Rewrite @runProc_map : sec.

(* Running A against S1 linked with S2 
   is equivalent to
   running A against S2, and running that result against S2 *)
Lemma runProc_LinkSys {O1 O2} {Out} {R} (A : Proc O1 R) (S1 : Sys O1 O2 unit) (S2 : Sys O2 EmptyOracle Out) s1 s2 : 
  runProc A (LinkSys S1 S2) (s1, s2) = 
    mapProc (runProc (runProc A S1 s1) S2 s2) (fun '(x, y, z) => (x, (y, z))).
  revert s1 s2; induction A; intros.
  {
  simpl.
  unfold mapProc; simpl.
  auto.
  }
  {
    simpl.
    autorewrite with sec.
    destruct (force (runProc (run S1 s1 q) S2 s2)).
    destruct p0.
    simpl.
    rewrite H.
    autorewrite with sec.
    auto.
  }
Qed.

Lemma force_let_pair {A B} {R} (p : A * B) (k : A -> B -> Proc EmptyOracle R) : 
  force (let '(x, y) := p in k x y) = 
  let '(x, y) := p in force (k x y).
  destruct p.
  auto.
Qed.
Hint Rewrite @force_let_pair : sec.

(* LinkSys is associative *)
Lemma LinkSys_assoc {O1 O2 O3} {Out} (S1 : Sys O1 O2 unit) (S2 : Sys O2 O3 unit) (S3 : Sys O3 EmptyOracle Out) s1 s2 s3 : 
  EquivSys (LinkSys (LinkSys S1 S2) S3)
           (LinkSys S1 (LinkSys S2 S3))
           ((s1, s2), s3)
           (s1, (s2, s3)).
  intro A.
  revert s1 s2 s3.
  induction A.
  {
    auto.
  }
  {
     intros; simpl.
     unfold runProcOut in *.
     simpl.
     rewrite runProc_LinkSys.
     autorewrite with sec.
     destruct (force (runProc (runProc _ _ _) _ _)).
     destruct p0.
     destruct p0.
     simpl.
     specialize (H r s4 s0 s).
     autorewrite with sec in H.
     simpl in *.
     remember (force (runProc (p r) (LinkSys (LinkSys S1 S2) S3) (s4, s0, s))) as res.
     simpl in *.
     rewrite <- Heqres.
     rewrite <- Heqres in H.
     destruct res.
     destruct p0.
     simpl in H.
     rewrite H.
     auto.
  }
Qed.

(* LinkSys is a left congruence for EquivSys *)
Lemma EquivSys_cong {O1 O2} {Out} (S1 : Sys O1 EmptyOracle Out) (S2 : Sys O1 EmptyOracle Out) s1 s2 (C : Sys O2 O1 unit) c : 
  EquivSys S1 S2 s1 s2 -> 
  EquivSys (LinkSys C S1) (LinkSys C S2) (c, s1) (c, s2).
  intros.
  intro.
  unfold runProcOut.
  autorewrite with sec.
  rewrite runProc_LinkSys.
  autorewrite with sec.
  simpl.
  unfold EquivSys in H.
  specialize (H (mapProc (runProc A C c) fst)).
  unfold runProcOut in H.
  autorewrite with sec in H.
  destruct (force (runProc (runProc A C c) S1 s1)).
  simpl in *.
  destruct p.
  simpl in *.
  rewrite H.
  rewrite runProc_LinkSys.
  autorewrite with sec.
  destruct (force (runProc (runProc A C c) S2 s2)).
  simpl.
  destruct p.
  simpl.
  auto.
Qed.

(* The above implies that Instantiates is transitive *)
Lemma InstTr {O1 O2 O3} {Out} {Secret}
             (S1 : Sys O1 EmptyOracle Out)
             (S2 : Sys O2 EmptyOracle Out)
             (S3 : Sys O3 EmptyOracle Out)
             (st1 : Secret -> _) st2 st3 : 
  Instantiates S1 S2 st1 st2 -> 
  Instantiates S2 S3 st2 st3 -> 
  Instantiates S1 S3 st1 st3.
  intros.
  destruct H as [C1 [c1 H1]].
  destruct H0 as [C2 [c2 H2]].
  exists (LinkSys C1 C2).
  exists (c1, c2).
  intro.
  eapply EquivSys_tr.
  apply H1.
  apply EquivSys_sym.
  eapply EquivSys_tr.
  apply LinkSys_assoc.
  apply EquivSys_sym.
  apply EquivSys_cong.
  apply H2.
Qed.

