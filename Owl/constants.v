Record Lattice := {
  labels : Set;
  leq : labels -> labels -> bool
  bot : labels;
}.

Axiom L : Lattice. 
