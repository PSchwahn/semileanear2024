import Semileanear2024.sylow.action
import Semileanear2024.sylow.sylow_defs

namespace Semileanear

variable (p : ℕ) (G : Type u) (pp : Prime p) [Group G] [Finite G] (r : ℕ) (h : isHighestPowerOfP (Nat.card G) p r) (m : ℕ) (h2 : Nat.card G = Nat.mul (p^r) m)

def alpha_g (g : G) (h : G) : G := (g ~ h) ~ g⁻¹

instance alpha : GroupAction G (Sylow p G) := by sorry
  -- mul := fun (g : G) (S : Sylow p G) => {y : G | ∃ s, s ∈ S.carrier ∧ (alpha_g g s) = y }
  -- one_id :
  -- assoc :




theorem orbit_alpha_divides_m (Q : Sylow p G) : Nat.card (orbit Q (alpha p G)) ∣ m := by sorry

end Semileanear
