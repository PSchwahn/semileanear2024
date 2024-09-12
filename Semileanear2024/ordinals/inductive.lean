import Mathlib

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

namespace Semileanear2024

--lean version of Nat is just an inductive type:

inductive ourNat where
  | zero : ourNat
  | succ : ourNat → ourNat
  deriving Repr

open ourNat

def add (m n : ourNat) : ourNat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

#eval add (succ (succ zero)) (succ zero)

-- limit ordinal: hard to define. need < relation and ordinal-indexed sequence
-- inductive types, induction principle/tactic for Nat, then transfinite induction?

--this will be the underlying type for omega + 1:
inductive NatAndAnother where
  | natural (n : ℕ) : NatAndAnother
  | another : NatAndAnother

--everything besides `another` has a successor
def NatAndAnother.succ (x : NatAndAnother) (xnat : x ≠ another) : NatAndAnother :=
  match x with
  | another => False.elim (by simp at xnat)
  | natural n => natural (Nat.succ n)

inductive NatAndAnother.le (n : NatAndAnother) : NatAndAnother → Prop
  | refl : le n n
  | aright : le n another
  | step {m} (hm : m ≠ another) : le n m → le n (succ m hm)
--is this right?

--induction principle
--why can't we just have one induction? positivity principle?
example (x : NatAndAnother) : 1 = 1 := by
  induction x with
  | another => sorry
  | natural n => induction n with
    | zero => sorry
    | succ k => sorry

end Semileanear2024
