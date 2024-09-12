import Semileanear2024.ordinals.inductive

open Semileanear2024

#check IsWellOrder
-- a well order is a TOTAL ORDER which is WELL-FOUNDED, i.e. every nonempty subset
-- has a least element.
-- A value is accessible if for all `y` such that `r y x`, `y` is also accessible.
-- r is well-founded iff any element is accessible.
--define relations, orders, well-orders
--some examples for well orders: Fin n, Nat, omega+1
#check wellOrderSucc
#check IsWellOrderLimitElement
-- limit element: neither a successor nor smallest element

#check Ordinal
-- quotient type of well-orderings on Type by order isomorphism

--ordinal addition
--limit ordinals
--transfinite induction?
#check Ordinal.addMonoidWithOne
#check Ordinal.partialOrder
#check Ordinal.induction
--use induction tactic with ordinals?
