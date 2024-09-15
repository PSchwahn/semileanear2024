import Semileanear2024.sylow.product

namespace Semileanear

open Finset

section finset

variable {G : Type u} [Group G] [finG : Fintype G]
variable (S : Set G) [DecidablePred S]

def finset_of_subset : Finset G := filter S finG.elems

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

variable (p : ℕ)

def IsPGroup (H : Subgroup G) : Prop := ∃ k : ℕ, card (finset_of_subset H.carrier) = p ^ k

theorem PGroups_intersection (H K : Subgroup G) (hH : IsPGroup p H) (hK : IsPGroup p K) :
    IsPGroup p (subgroup_of_intersection H K) := sorry

theorem lem9 (hp : Nat.Prime p) (H K : Subgroup G) (hH : IsPGroup p H) (hK : IsPGroup p K) :
    ∃ l : ℕ, card (finset_of_subset (ProductOfSubgroups H K)) = p ^ l := by
  rcases PGroups_intersection p H K hH hK with ⟨kI, hI⟩
  rcases hH with ⟨kH, hH⟩
  rcases hK with ⟨kK, hK⟩
  use kH + kK - kI
  have := lem8 H K
  dsimp[subgroup_of_intersection] at hI
  rw [hH, hK, hI, ←pow_add] at this
  rw [←@Nat.mul_div_left (card (finset_of_subset (ProductOfSubgroups H K))) (p^kI) (Nat.pow_pos (Nat.Prime.pos hp)), this]
  rw [Nat.pow_div]
  swap
  exact Nat.Prime.pos hp
  calc kI ≤ kH := ?_
    _ ≤ kH + kK := Nat.le_add_right kH kK
  rw [←Nat.pow_le_pow_iff_right (Nat.Prime.one_lt hp), ←hI, ←hH]
  apply card_le_card
  dsimp [finset_of_subset]
  apply monotone_filter_right
  change H.carrier ∩ K.carrier ⊆ H.carrier
  apply Set.inter_subset_left

end fingroup
