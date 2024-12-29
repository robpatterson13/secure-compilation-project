Inductive Empty := .

Record Oracles := {
    query : Type;
    response : query -> Type
}.

Definition EmptyOracle : Oracles :=
  {| query := Empty; response := fun x => match x with end |}.

(* A Proc is an interactive computation 
that can make queries according to oracles in O. *)
Inductive Proc (O : Oracles) (A : Type) :=
  | PRet : A -> Proc O A
  | PQuery (q : O.(query)) : 
             (O.(response) q -> Proc O A) ->
             Proc O A.

Arguments PRet [O A].
Arguments PQuery [O A].

(* A Proc that uses no oracles is equivalent to a pure value. *)
Definition force {A} (P : Proc EmptyOracle A) : A :=
  match P with
    | PRet x => x 
    | PQuery q _ => match q with end end. 

(* Sequential composition operator on procs *)
Fixpoint bind {O} {A B} (c : Proc O A) (k : A -> Proc O B) :=
  match c with
    | PRet x => k x
    | PQuery q f => PQuery q (fun x => bind (f x) k) end.

(* Map over procs *)
Definition mapProc {O} {A B} (c : Proc O A) (f : A -> B) :=
  bind c (fun x => PRet (f x)).

(* A Sys is an interactive, stateful machine that handles 
queries from O1, and produces queries in O2.  *)

(* Additionally, each Sys has a type of _outputs_ that come from its internal state. *)
Record Sys (O1 O2 : Oracles) Out := { 
    state : Type;
    run : state -> forall (q : O1.(query)), 
          Proc O2 (state * O1.(response) q);
    output : state -> Out
}.

Arguments state [O1 O2 Out].
Arguments run [O1 O2 Out].
Arguments output [O1 O2 Out].

(* We can run a Proc against a Sys: 
   the Sys handles the queries coming from the Proc, and we end up 
   with a Proc that asks for the queries that the Sys asks for. *)
Fixpoint runProc {O1 O2 : Oracles} {Out} {R} (A : Proc O1 R) 
  (S : Sys O1 O2 Out) (st : S.(state)) : Proc O2 (R * S.(state)) :=
  match A with
    | PRet x => PRet (x, st)
    | PQuery q k => 
        bind (S.(run) st q) (fun '(st', r) => 
           runProc (k r) S st') end.

(* This just runs the Proc and extracts the external output, rather than the intermediate state. *) 
Definition runProcOut {O1 O2 : Oracles} {Out} {R} (A : Proc O1 R) 
  (S : Sys O1 O2 Out) (st : S.(state)) : Proc O2 (R * Out) :=
  mapProc (runProc A S st) (fun '(x, y) => (x, S.(output) y)).

(* Two systems are _equivalent_, or _indistinguishable_, 
   if, for any attacker A that interacts with the two systems, 
   the attacker's output  and the external output 
   of the system is the same. 

  The two states s1 and s2 are the initial states.
*)
Definition EquivSys {O} {Out} (S1 S2 : Sys O EmptyOracle Out) (s1 : S1.(state)) (s2 : S2.(state)) :=
  forall (A : Proc O bool), 
    force (runProcOut A S1 s1) = 
    force (runProcOut A S2 s2).


(* We can plug two systems together, taking the external output of the second one. The external output of the inner system must be trivial (i.e., unit) *) 
Definition LinkSys {O1 O2 O3 : Oracles} {Out}
                   (S1 : Sys O1 O2 unit)
                   (S2 : Sys O2 O3 Out)
                   : Sys O1 O3 Out:= 
  {| 
    state := S1.(state) * S2.(state);
    run := fun '(s1, s2) q => 
             mapProc (runProc (S1.(run) s1 q) S2 s2)
                     (fun '(x, y, z) => (x, z, y));
    output := fun '(_, s) => S2.(output) s |}.
             

(* The main definition of security. 
Let S1 and S2 be two systems that respond to queries over oracles 
O1 and O2, respectively, but don't make queries themselves.
We think of these two systems as giving a certain amount of "leakage"
to adversaries. The adversary's job is to figure out a certain secret 
hidden inside the system's state while making queries to these two systems. 

Then, we say that S1 instantiates S2 if there exists a _simulator_
Sim that translates queries in O1 to queries in O2, such that:
-  no adversary can tell the difference between S1 and Sim + S2; and
-  no adversary can make S1 and Sim + S2 differ on its final return value.

In other words, we prove that any observation the adversary can make against 
S1 can be made against S2 as well, by using the simulator.
*)

(* To encode systems that hold secrets, we consider _functions_ from secrets to states of the systems. Then, we require that a simulator exists that works for all choices of secret. This means the simulator cannot learn the secret (except perhaps through querying the system). *)
Definition Instantiates {O1} {O2} {Out} {Secret} 
  (S1 : Sys O1 EmptyOracle Out) (S2 : Sys O2 EmptyOracle Out)
  (st1 : Secret -> S1.(state))
  (st2 : Secret -> S2.(state))
  :=
  exists Sim : Sys O1 O2 unit, 
    exists cst,
      forall secret, 
        EquivSys S1 (LinkSys Sim S2) (st1 secret) (cst, st2 secret).
