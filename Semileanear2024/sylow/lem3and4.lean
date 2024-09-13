import Semileanear2024.sylow.basic

namespace Semileanear

section toGroup

variable {G : Type u} [instG : Group G] (H : Subgroup G)

def Subgroup.toGroup : Type u := { x // x ∈ H.carrier}

instance : Group (Subgroup.toGroup H) where
  mul := by {
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    use a ~ b
    exact H.mul_mem' ha hb
  }
  mul_assoc := by {
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    apply Subtype.ext
    apply instG.mul_assoc
  }
  one := by {
    use instG.one
    exact H.one_mem'
  }
  one_mul := by {
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply instG.one_mul
  }
  mul_one := by {
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply instG.mul_one
  }
  inv := by {
    rintro ⟨a, ha⟩
    use a⁻¹
    exact H.inv_mem' ha
  }
  mul_inv_cancel := by {
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply instG.mul_inv_cancel
  }
  inv_mul_cancel := by {
    rintro ⟨a, ha⟩
    apply Subtype.ext
    apply instG.inv_mul_cancel
  }

end toGroup

--Lemma 3 und 4:

section Lem34

variable (G : Type u) [Group G] (H K : Subgroup G)

#check H.toGroup
#check Subgroup (H.toGroup) --geht!

instance lem4 (h : H.carrier ⊆ K.carrier) : Subgroup (K.toGroup) where
  carrier := { x | x.1 ∈ H.carrier }
  mul_mem' := by {
    rintro ⟨a, _⟩ ⟨b, _⟩ ha hb
    change a ∈ H.carrier at ha
    change b ∈ H.carrier at hb
    change a ~ b ∈ H.carrier
    exact H.mul_mem' ha hb
  }
  one_mem' := by {
    simp
    exact H.one_mem'
  }
  inv_mem' := by {
    rintro ⟨a, _⟩ ha
    change a ∈ H.carrier at ha
    change a⁻¹ ∈ H.carrier
    exact H.inv_mem' ha
  }

instance subgroup_of_intersection : Subgroup G := {
  carrier := H.carrier ∩ K.carrier
  mul_mem' := by {
    rintro a b ⟨haH, haK⟩ ⟨hbH, hbK⟩
    constructor
    exact H.mul_mem' haH hbH
    exact K.mul_mem' haK hbK
  }
  one_mem' := by {
    simp
    exact ⟨H.one_mem', K.one_mem'⟩
  }
  inv_mem' := by {
    intro x hx
    change x ∈ H.carrier ∩ K.carrier at hx
    simp
    exact ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩
  }
}

instance lem3 : Subgroup (H.toGroup) := lem4 G (subgroup_of_intersection G H K) H (by {
  change H.carrier ∩ K.carrier ⊆ H.carrier
  rintro x ⟨hxH, _⟩
  exact hxH
})

end Lem34
