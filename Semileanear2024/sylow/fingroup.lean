import Semileanear2024.sylow.product

namespace Semileanear

open Finset

section finset

variable {G : Type u} [Group G] [finG : Fintype G]
variable (S : Set G) [DecidablePred S]

def finset_of_subset : Finset G := filter S finG.elems

--instance : Fintype H.toGroup where
--  elems := sorry
--  complete := sorry
--or Fintype H.carrier?

#check card (finset_of_subset S)

end finset

section fingroup

open Classical
--Wir brauchen klassische Logik, damit jede Proposition ENTSCHEIDBAR wird.
--D.h. für jede Proposition gibt es einen Beweis, dass sie wahr oder falsch ist.
--Das wird benötigt, damit Teilmengen von Finsets wieder Finsets werden.

variable {G : Type u} [Group G] [finG : Fintype G]

theorem lem8 (H K : Subgroup G) : card (finset_of_subset (ProductOfSubgroups H K))
    * card (finset_of_subset (H.carrier ∩ K.carrier))
    = card (finset_of_subset H.carrier) * card (finset_of_subset K.carrier) := sorry

--eine p-untergruppe ist eine untergruppe von ordnung p^s mit s ≤ r.
-- G ist von der Größe p^r * m.

variable (p : ℕ) (hp : Nat.Prime p)

def IsPGroup (H : Subgroup G) : Prop := ∃ k : ℕ, card (finset_of_subset H.carrier) = p ^ k

theorem lem9 (H K : Subgroup G) (hH : IsPGroup H) (hK IsPGroup K) :
    ∃ l : ℕ, card (finset_of_subset (ProductOfSubgroups H K)) = p ^ l := sorry

end fingroup
