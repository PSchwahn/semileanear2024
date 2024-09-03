import Mathlib

--idea: first try to define ordinals, addition, transfinite induction etc. from scratch, just starting with Nat
--look up resources on ordinals
--other idea: showcase Mathlib implementation / compare with naive idea.
--introduce important Lean/Mathlib concepts (universes, quotients etc.) along the way
--review ℕ

/-
POSSIBLE DEFINITIONS:

-Equivalence classes of well-orderings. This is used in Principia mathematica,
 but does not fit into (axiomatic, e.g. ZF) set theory because the equivalence classes
 are too large to be sets. However it is possible in type theory, and in fact used in Mathlib.

-von Neumann ordinals: The set-theoretic version. It continues the von Neumann construction
 of the naturals.
 A set S is an ordinal if and only if S is strictly well-ordered with respect to set membership
 and every element of S is also a subset of S.
 Doesn't work well since set membership is not a fundamental relation in type theory, and subsets
 cannot really be elements. Taking type judgement instead makes even less sense.

-inductive type: works for Nat but is problematic for limit ordinals because it presupposes
 the relation <, so we kind of have a circle argument.
-/

--lean version of Nat is just an inductive type:
inductive ourNat where
  | zero : ourNat
  | succ (o : ourNat) : ourNat
-- limit ordinal: hard to define. need < relation and ordinal-indexed sequence

#check IsWellOrder
