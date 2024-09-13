import Semileanear2024.sylow.beta

namespace Semileanear


variable (p : ℕ) (G : Type u) (pp : Prime p) [Group G] [Finite G] (r : ℕ) (h : isHighestPowerOfP (Nat.card G) p r) (m : ℕ) (h2 : Nat.card G = Nat.mul (p^r) m)

--Satz a)
theorem sylow_nonempty : Nonempty (Sylow p G) := by sorry


--Satz b)
theorem pGroupSubgroupOfSylow (U : Subgroup G) (isp : IsPGroup p U.carrier) : ∃ (P : Sylow p G), U.carrier ⊆ P.carrier := by sorry

--Satz c)
theorem alpha_transitive : isTransitive G (Sylow p G) (alpha p G) := by sorry

--Satz d)
theorem spDividesM : Nat.card (Sylow p G) ∣ m := by sorry

--Satz e)
theorem spModPEqOne : Nat.card (Sylow p G) ≡ 1 [MOD p] := by sorry

end Semileanear
