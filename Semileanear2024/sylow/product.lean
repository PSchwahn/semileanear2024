import Semileanear2024.sylow.basic
import Semileanear2024.sylow.lem3and4

namespace Semileanear

section sectionProduct

variable {G : Type u}[instG : Group G](H K : Subgroup G)

def conjug (g : G) (h : G) : G := (g ~ h) ~ g⁻¹

def conjug_subset (g : G) (P : Set G) : Set G := (conjug g) '' P
-- f '' P is the image of (P : Set G) under (f : G → ...)

def lem5 (h5 : ∀ u ∈ H.carrier, conjug_subset u K.carrier = K.carrier) : Subgroup G where
  carrier := ProductOfSubgroups H K
  mul_mem' := by {
    rintro a b ⟨aH, aK, haH, haK, ha⟩ ⟨bH, bK, hbH, hbK, hb⟩
    change ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ a ~ b = h ~ k
    let p := (bH⁻¹ ~ aK) ~ bH
    have : p ∈ K.carrier := by {
      dsimp [p]
      specialize h5 bH⁻¹ (H.inv_mem' hbH)
      rw [←h5]
      use aK, haK
      dsimp [conjug]
      rw [inv_inv]
    }
    use aH ~ bH, p ~ bK, H.mul_mem' haH hbH, K.mul_mem' this hbK
    rw [ha, hb]
    dsimp [p]
    calc aH ~ aK ~ (bH ~ bK) = aH ~ instG.one ~ aK ~ (bH ~ bK) := by rw [instG.mul_one]
      _ = aH ~ (bH ~ bH⁻¹) ~ aK ~ (bH ~ bK) := by rw [instG.mul_inv_cancel]
      _ = aH ~ bH ~ bH⁻¹ ~ aK ~ (bH ~ bK) := by rw [instG.mul_assoc aH bH]
      _ = aH ~ bH ~ bH⁻¹ ~ (aK ~ (bH ~ bK)) := by rw [instG.mul_assoc]
      _ = aH ~ bH ~ bH⁻¹ ~ (aK ~ bH ~ bK) := by rw [instG.mul_assoc aK]
      _ = aH ~ bH ~ (bH⁻¹ ~ (aK ~ bH ~ bK)) := by rw [instG.mul_assoc]
      _ = aH ~ bH ~ (bH⁻¹ ~ (aK ~ bH) ~ bK) := by rw [instG.mul_assoc bH⁻¹]
      _ = aH ~ bH ~ (bH⁻¹ ~ aK ~ bH ~ bK) := by rw [instG.mul_assoc bH⁻¹ aK]
  }
  one_mem' := by {
    change ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ instG.one = h ~ k
    use instG.one, instG.one, H.one_mem', K.one_mem'
    rw [instG.one_mul]
  }
  inv_mem' := by {
    intro x
    intro hypx
    simp at hypx
    simp
    change (∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ x = h ~ k) at hypx
    cases' hypx with h1 hyp1
    cases' hyp1 with k1 hyp2
    cases' hyp2 with hyph hyp3
    cases' hyp3 with hypk hyp4
    change (∃ h' k', h' ∈ H.carrier ∧ k' ∈ K.carrier ∧ x⁻¹ = h' ~ k')
    use h1⁻¹
    use conjug h1 k1⁻¹
    constructor
    apply H.inv_mem'
    exact hyph
    constructor
    have hyp5 := h5
    specialize hyp5 h1
    apply hyp5 at hyph
    rw [← hyph]
    change conjug h1 k1⁻¹ ∈ (conjug (h1)''K)
    simp
    use k1⁻¹
    constructor
    apply K.inv_mem'
    exact hypk
    rfl
    rw [hyp4]
    change ((h1 ~ k1)⁻¹ = h1⁻¹ ~ ((h1 ~ k1⁻¹) ~ h1⁻¹))
    rw[instG.mul_assoc]
    rw[← instG.mul_assoc]
    rw[instG.inv_mul_cancel]
    rw[instG.one_mul]
    rw[inv_of_prod]
  }

theorem lem6 : K.carrier ⊆ ProductOfSubgroups H K := by {
  change ∀ k ∈ K.carrier, k ∈ ProductOfSubgroups H K
  intro h1 h2
  change  ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ h1 = h ~ k
  use One.one, h1
  constructor
  exact H.one_mem'
  constructor
  exact h2
  rw [MulOneClass.one_mul]
}

def lem7 (h7 : ProductOfSubgroups H K = K.carrier) : Subgroup K.toGroup := lem4 H K (by {
  intro h hh
  rw [←h7]
  use h, instG.one, hh, K.one_mem'
  rw [instG.mul_one]
})

def inv_unique (g h1 h2 : G)(hyp: g ~ h1 = instG.one ∧ h1 ~ g = instG.one ∧ g ~ h2 = instG.one ∧ h2 ~ g = instG.one) : (h1 = h2) := by {
  cases' hyp with hyp1 hyp
  cases' hyp with hyp2 hyp
  cases' hyp with hyp3 hyp4
  rw [← instG.mul_one h1, ← hyp3, ← instG.mul_assoc, hyp2, instG.one_mul]
}

def inv_of_prod (g1 g2 : G) : ((g1 ~ g2)⁻¹ = g2⁻¹ ~ g1⁻¹) := by {
  have hyp := inv_unique (g1 ~ g2) (g1 ~ g2)⁻¹ (g2⁻¹ ~ g1⁻¹)
  apply hyp
  constructor
  apply instG.mul_inv_cancel
  constructor
  apply instG.inv_mul_cancel
  constructor
  rw [instG.mul_assoc]
  nth_rw 2 [← instG.mul_assoc]
  rw [instG.mul_inv_cancel]
  rw [instG.one_mul]
  rw [instG.mul_inv_cancel]
  rw [instG.mul_assoc]
  nth_rw 2 [← instG.mul_assoc]
  rw [instG.inv_mul_cancel, instG.one_mul, instG.inv_mul_cancel]
}

end sectionProduct

end Semileanear
