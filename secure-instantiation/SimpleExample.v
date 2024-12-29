Require Import AbstractSecurity AbstractSecurityLemmas Arith Lia.

(* Here, we show an example proof of instantiation. *)

Inductive CounterQuery := Step.

Definition StepOracle : Oracles :=
  {| query := CounterQuery; response := 
      fun _ => nat (* Leak the parity of the number *)
  |}.

(* We have two example systems. 
   Both hold a secret integer.
   The adversary can query each system, and the system will leak the parity (whether even or odd) of the secret number. *)
   

(* In the first system, the integer increments by 1 each time the adversary queries it. The external output of the system is its state multiplied by 2. *)
Definition CountBy1 : Sys StepOracle EmptyOracle nat :=
  {|
    state := nat; 
    run := fun i (q : StepOracle.(query)) => 
             PRet (i + 1, i mod 2);
    output := fun i => (i * 2) |}.

(* In the second system, the integer increments by 2. The external output of the system is the state. *)
Definition CountBy2 : Sys StepOracle EmptyOracle nat :=
  {|
    state := nat; 
    run := fun i (q : StepOracle.(query)) => 
             PRet (i + 2, 0); (* Don't leak parity *)
    output := fun i => i |}.

(* Now, notice that while the first state leaks the parity, while the
second state doesn't, the parity of the integer is actually
reconstructible using only information knowable to the adversary.
Assuming that the secret integer starts at an even number, 
we have that the parity will always be 0, 1, 0, 1, ....

Thus, even though CountBy1 is more "leaky" about the secret
(we leak the parity bit which depends on the secret state),
this leaked information is actually not leaking anything at all.
 *)

(* Thus, we have the simulator keep track of some internal state to
   remember what the parity is. *)
Definition CountBy2Sim : Sys StepOracle StepOracle unit :=
  {| state := nat; 
     run := fun i (q : StepOracle.(query)) => 
              (* When the adversary queries CountBy1, 
                 the simulator queries CountBy2 accordingly,
                 and returns the reconstructed parity bit. *)
              match q return Proc StepOracle _ with
                | Step => 
                    PQuery (Step : query StepOracle) (fun r => PRet (1 - i, i))
              end;
     output := fun _ => tt |}.


(* a basic lemma about mod 2 that is important *)
Lemma mod_2_spec i : 
  i mod 2 = if Nat.even i then 0 else 1.
  induction i.
  auto.
  replace ((S i) mod 2) with ((1 + i) mod 2).
  2: {
    auto.
  }
  rewrite Nat.Div0.add_mod.
  rewrite IHi.
  replace (Nat.even (S i)) with (negb (Nat.even i)).
  2: {
    rewrite Nat.even_succ.
    rewrite <- Nat.negb_even.
    auto.
    }
  destruct (Nat.even i).
  auto.
  auto.
Qed.


(* We now do the proof that CountBy1 instantiates CountBy2.
 *)

(* We encode the assumtion that the secret is even by having 
the set of secrets be EvenNat; i.e., nats that carry a proof that they
are even. *)
Definition EvenNat := {n : nat | Nat.even n = true}.


Theorem CountBy1Refines : Instantiates CountBy1 CountBy2 

                            (fun (i : EvenNat) => proj1_sig i)
                            (fun (i : EvenNat) => 2 * proj1_sig i).
  exists CountBy2Sim.
  (* Initial state of simulator is zero *)
  exists 0.
  intro.
  eapply EquivBisim.
  
  (* The bisimulation relation is between CountBy1 and the composition of CountBy2Sim with CountBy2.
     
     The relation states that CountBy2's state is 2 times CountBy1's state,
     and the parity state held inside of CountBy2Sim is correct. *)
  instantiate (1 := fun i '(par, i2) => 
                      i2 = i * 2 /\
                      par = i mod 2).

  (* This helps the rewriting *)
  Opaque Nat.modulo.

  3: {
    (* We first need to show that the bisimulation relation holds 
       on initial states, for all choices of secret *)
    simpl.
    destruct secret.
    simpl.
    intuition.
    rewrite mod_2_spec.
    rewrite e; auto.
  }
  {
    (* We next show that the two related states generate the same outputs. *)
    simpl.
    intros s1 [par s2].
    intuition.
  }
  {
    (* Finally, we show that the two related states stay related, and produce the same responses, when the adversary queries them. *)
    intros s1 [par s2].
    intuition.
    simpl.
    destruct q.
    simpl.
    split.
    split.
    lia.
    subst.
    rewrite mod_2_spec.
    rewrite mod_2_spec.
    rewrite Nat.even_add.
    destruct (Nat.even s1).
    auto.
    auto.
    intuition.
  }
Qed.
