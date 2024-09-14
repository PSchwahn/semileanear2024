import Semileanear2024.sylow.basic
import Semileanear2024.sylow.lem3and4

namespace Semileanear

-- 1.3 Produkt von U-Gruppen

section sectionProduct

variable {G : Type u} [instG : Group G] (H K : Subgroup G)

def ProductOfSubgroups := {g : G | ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ g = h ~ k}

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
    calc aH ~ aK ~ (bH ~ bK) = aH ~ One.one ~ aK ~ (bH ~ bK) := by rw [instG.mul_one]
      _ = aH ~ (bH ~ bH⁻¹) ~ aK ~ (bH ~ bK) := by rw [instG.mul_inv_cancel]
      _ = aH ~ bH ~ bH⁻¹ ~ aK ~ (bH ~ bK) := by rw [instG.mul_assoc aH bH]
      _ = aH ~ bH ~ bH⁻¹ ~ (aK ~ (bH ~ bK)) := by rw [instG.mul_assoc]
      _ = aH ~ bH ~ bH⁻¹ ~ (aK ~ bH ~ bK) := by rw [instG.mul_assoc aK]
      _ = aH ~ bH ~ (bH⁻¹ ~ (aK ~ bH ~ bK)) := by rw [instG.mul_assoc]
      _ = aH ~ bH ~ (bH⁻¹ ~ (aK ~ bH) ~ bK) := by rw [instG.mul_assoc bH⁻¹]
      _ = aH ~ bH ~ (bH⁻¹ ~ aK ~ bH ~ bK) := by rw [instG.mul_assoc bH⁻¹ aK]
  }
  one_mem' := by {
    change ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ One.one = h ~ k
    use instG.one, instG.one, H.one_mem', K.one_mem'
    rw [instG.one_mul]
  }
  inv_mem' := by {
    rintro a ⟨aH, aK, haH, haK, ha⟩
    change ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ a⁻¹ = h ~ k
    sorry
  }


--

--Konjugation
def Konjug (g : G) (h : G) : G := (g ~ h) ~ g⁻¹ --Konjugation als G-Wirkung

def KonjugSubSet (h : G) (P : Set G) : Set G := (Konjug h)''P  --Bild von Konjugation

--

def ProductOfSubgroups (H K : Subgroup G) := {g : G | ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ g = h ~ k} --Definition 1

def Lem5 (h5: ∀ h ∈ H.carrier, KonjugSubSet h K.carrier = K.carrier) : Subgroup G
where
  carrier := ProductOfSubgroups H K
  mul_mem' := sorry
  inv_mem' := sorry
  one_mem' := by {
    simp
    change ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ One.one = h ~ k
    use One.one, One.one
    constructor
    exact H.one_mem'
    constructor
    exact K.one_mem'
    rw [MulOneClass.one_mul]
  }

def Lem6: K.carrier ⊆ ProductOfSubgroups H K := by {
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

def Lem7 (h7: ProductOfSubgroups H K = K.carrier) : Subgroup K.toGroup
where
  carrier :=  {x | x.1 ∈ H.carrier}
  mul_mem' := sorry
  inv_mem' := sorry
  one_mem' := sorry

end sectionProduct

end Semileanear
