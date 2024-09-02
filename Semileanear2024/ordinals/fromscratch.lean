import Mathlib

--idea: first try to define ordinals, addition, transfinite induction etc. from scratch, just starting with Nat
--look up resources on ordinals
--other idea: showcase Mathlib implementation / compare with naive idea.
--introduce important Lean/Mathlib concepts (universes, quotients etc.) along the way

/-
POSSIBLE DEFINITIONS:

-Equivalence classes of well-orderings. This is used in Principia mathematica,
 but does not fit into (axiomatic, e.g. ZF) set theory because the equivalence classes
 are too large to be sets. However it is possible in type theory, and in fact used in Mathlib.

-von Neumann ordinals: The set-theoretic version. It continues the von Neumann construction
 of the naturals.
-/
def best_number := (1 : ℕ)
