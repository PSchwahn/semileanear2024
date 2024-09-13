import Semileanear2024.ordinals.inductive

open Semileanear2024

#check IsWellOrder
-- a well order is a TOTAL ORDER which is WELL-FOUNDED.
-- TOTAL ORDER (< version) is equivalent to trichotomous and transitive.
-- WELL-FOUNDED (set theory): every nonempty subset has a least element.
-- WELL-FOUNDED (type theory): any term is accessible.
-- A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
#check WellFounded
--define relations, orders, well-orders
--some examples for well orders: Fin n, Nat, omega+1
#check wellOrderSucc
#check IsWellOrderLimitElement
-- limit element: neither a successor nor smallest element

#check Ordinal
-- quotient type of well-orders by order isomorphism
#check Ordinal.type
-- the quotient map of well-orders into ordinals

--ordinal addition
--limit ordinals
--transfinite induction?
#check Ordinal.addMonoidWithOne
#check Ordinal.partialOrder
#check Ordinal.induction

--we can use induction tactic with ordinals:
variable (P : Ordinal → Prop)
variable (Pstep : ∀ (o : Ordinal), (∀ k < o, P k) → P o)
--idk what to take as an example, so I just used P.

example (o : Ordinal) : P o := by
  induction o using Ordinal.induction with
  | h i IH => {
    apply Pstep i
    exact IH
  }

--or without tactics:
example (o : Ordinal) : P o := by
  apply Ordinal.induction
  exact Pstep
