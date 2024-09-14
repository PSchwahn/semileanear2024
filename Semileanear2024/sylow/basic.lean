import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.NeZero

import Mathlib
-- import Paperproof



namespace Semileanear

section sectionBasic

class LAction (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  mul : α → β → γ



class MulAction (M : Type u) (α : Type v) extends LAction M α α

class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α


class Mul (M : Type u) extends LAction M M M


infixl:65 " ~ " => LAction.mul
postfix:max "⁻¹" => Inv.inv




class One (α : Type u) where
  one : α

-- instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
--   ofNat := ‹One α›.1

-- instance (priority := 20) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
--   one := 1



/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 ~ a = a` and `a ~ 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, one ~ a = a
  mul_one : ∀ a : M, a ~ one = a


/-- A semigroup is a type with an associative `(~)`. -/
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, (a ~ b) ~ c = a ~ (b ~ c)



class Monoid (M : Type u) extends Semigroup M, MulOneClass M



class Group (G : Type u) extends Monoid G, Inv G where
  inv_mul_cancel : ∀ a : G, a⁻¹ ~ a = one
  mul_inv_cancel : ∀ a : G, a ~ a⁻¹ = one




instance instMonoid : Monoid ℕ where
  mul := Nat.add
  mul_assoc := Nat.add_assoc
  one := Nat.zero
  one_mul := Nat.zero_add
  mul_one := Nat.add_zero



-- instance cyclicGroup (n : ℕ) [NeZero n] : Group (Fin n) where
--   mul := Fin.add
--   mul_assoc := {by simp [Fin.ext_iff, Fin.add_def, Nat.add_assoc] }
--   one := Fin.mk 0 (Nat.pos_of_neZero n)
--   one_mul := Fin.zero_add
--   mul_one := Fin.add_zero
--   inv := fun a ↦ Fin.mk ((n - a) % n) (Nat.mod_lt _ a.size_pos)
--   inv_mul_cancel := fun ⟨a, ha⟩ ↦
--       Fin.ext <| (Nat.mod_add_mod _ _ _).trans <| by
--       rw [Nat.sub_add_cancel, Nat.mod_self]
--       . apply rfl
--       . exact le_of_lt ha







/-- `MulMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(~)` -/
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a ~ b ∈ s

/-- `OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type*) (M : Type*) [instOne : One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (instOne.one : M) ∈ s


/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(~)` -/
class SubmonoidClass (S : Type*) (M : Type*) [MulOneClass M] [SetLike S M] extends MulMemClass S M, OneMemClass S M : Prop

/-- `InvMemClass S G` states `S` is a type of subsets `s ⊆ G` closed under inverses. -/
class InvMemClass (S G : Type*) [Inv G] [SetLike S G] : Prop where
  /-- `s` is closed under inverses -/
  inv_mem : ∀ {s : S} {x}, x ∈ s → x⁻¹ ∈ s


/-- `SubgroupClass S G` states `S` is a type of subsets `s ⊆ G` that are subgroups of `G`. -/
class SubgroupClass (S G : Type*) [Group G] [SetLike S G] extends SubmonoidClass S G, InvMemClass S G : Prop




/-- A subsemigroup of a magma `M` is a subset closed under multiplication. -/
structure Subsemigroup (M : Type u) [Mul M] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set M
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a ~ b ∈ carrier


/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type u) [instM : MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (instM.one : M) ∈ carrier


/-- A subgroup of a group `G` is a subset containing 1, closed under multiplication
and closed under multiplicative inverse. -/
structure Subgroup (G : Type u) [Group G] extends Submonoid G where
  /-- `G` is closed under inverses -/
  inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier



variable (M : Type u)

instance [Semigroup M] : SetLike (Subsemigroup M) M :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

instance [Semigroup M] : MulMemClass (Subsemigroup M) M where mul_mem := fun {_ _ _} => Subsemigroup.mul_mem' _


instance [Monoid M] : SetLike (Submonoid M) M where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective' h


instance [Monoid M] : SubmonoidClass (Submonoid M) M where
  one_mem (s) := s.one_mem'
  mul_mem {s} := s.mul_mem'


variable (G : Type u) [Group G]

instance : SetLike (Subgroup G) G where
  coe s := s.carrier
  coe_injective' p q h := by
    obtain ⟨⟨⟨hp,_⟩,_⟩,_⟩ := p
    obtain ⟨⟨⟨hq,_⟩,_⟩,_⟩ := q
    congr

instance : SubgroupClass (Subgroup G) G where
  inv_mem := Subgroup.inv_mem' _
  one_mem _ := (Subgroup.toSubmonoid _).one_mem'
  mul_mem := (Subgroup.toSubmonoid _).mul_mem'

end sectionBasic

section auxiliaryForGroup

variable {G : Type u} [instG : Group G]

theorem inv_inv (g : G) : g⁻¹⁻¹ = g := by
    have h1 : g⁻¹⁻¹ ~ g⁻¹ ~ g = g
    rw [Group.inv_mul_cancel, MulOneClass.one_mul]
    have h2 : g⁻¹⁻¹ ~ g⁻¹ ~ g = g⁻¹⁻¹
    rw [Semigroup.mul_assoc, Group.inv_mul_cancel, MulOneClass.mul_one]
    rw [← h2]
    nth_rewrite 4 [← h1]
    rfl

theorem inv_unique (g h1 h2 : G)(hyp: g ~ h1 = instG.one ∧ h1 ~ g = instG.one ∧ g ~ h2 = instG.one ∧ h2 ~ g = instG.one) : (h1 = h2) := by {
  cases' hyp with hyp1 hyp
  cases' hyp with hyp2 hyp
  cases' hyp with hyp3 hyp4
  rw [← instG.mul_one h1, ← hyp3, ← instG.mul_assoc, hyp2, instG.one_mul]
}

theorem inv_of_prod (g1 g2 : G) : ((g1 ~ g2)⁻¹ = g2⁻¹ ~ g1⁻¹) := by {
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

end auxiliaryForGroup

section sectionMengen

variable {α : Type*}
variable (H K : Finset α)


def lem1 (h : H ⊆ K) : H.card ≤ K.card := by {
  exact Finset.card_le_card h
}

def lem2 (h₁ : H ⊆ K) (h₂ : K.card = H.card) : H = K := by {
  apply Nat.le_of_eq at h₂
  apply Finset.eq_of_superset_of_card_ge at h₂
  rw [symm h₂]
  exact h₁
}


end sectionMengen

end Semileanear
