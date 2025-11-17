This serves as a sandbox for testing various things in Rocq.

This includes messing around with security lemmas, basic implementations of System F and STLC, plus proofs of non-interference for small languages

Ths most notable aspect of this project is in Owl folder, as it includes a partial mechanization of the language. It also includes inductives for typechecking and evaluation.
Importantly, there also exists a Fixpoint called ``exec``, which allows for execution of Owl terms to prove how they reduce. 
Finally, there are some additional lemmas about Owl such as ``well_bracketed`` that demonstrate neat features of the languages design. 
