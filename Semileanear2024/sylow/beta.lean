
import Semileanear2024.sylow.alpha

namespace Semileanear


variable (p : ℕ) (G : Type u) (pp : Prime p) [Group G] [Finite G] (r : ℕ) (h : isHighestPowerOfP (Nat.card G) p r) (m : ℕ) (h2 : Nat.card G = Nat.mul (p^r) m)


variable (U : Subgroup G) [Group U] (isp : IsPGroup p U)

--def Q : Sylow p G := by sorry

variable (Q : Sylow p G)

instance beta : GroupAction U (orbit Q (alpha p G)) := by sorry

theorem card_eq_one_or_p_divides (Q : Sylow p G) (P :  orbit Q (alpha p G)):
    (1 =  Nat.card (orbit P (beta p G U Q)))
  ∨ (p ∣  Nat.card (orbit P (beta p G U Q))) := by sorry


end Semileanear
