Record Lattice := {
  labels : Set;
  leq : labels -> labels -> bool;
  bot : labels;
  join : labels -> labels -> labels;
  meet : labels -> labels -> labels;
}.

Axiom L : Lattice. 
