import Semileanear2024.sylow.basic


namespace Semileanear


variable (p : ℕ) (G : Type u) [Group G] [Finite G]

def IsPGroup (p : ℕ) (α : Type u) : Prop := ∃ n : ℕ, Nat.card α = p ^ n


def isHighestPowerOfP (n p r : Nat) : Prop := p^r ∣ n ∧ ¬ p^(r+1) ∣ n




variable (p : ℕ) (G : Type u) (pp : Prime p) [Group G] [Finite G] (r : ℕ) (h : isHighestPowerOfP (Nat.card G) p r) (m : ℕ) (h2 : Nat.card G = Nat.mul (p^r) m)

class Sylow extends Subgroup G where
  order : ∃ r : ℕ, Nat.card carrier = p ^ r ∧ isHighestPowerOfP (Nat.card G) p r


end Semileanear
