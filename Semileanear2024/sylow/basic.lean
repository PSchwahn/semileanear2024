import Mathlib.Data.Nat.Defs
import Mathlib.Algebra.NeZero

import Mathlib



namespace Semileanear

section sectionBasic

class LAction (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  mul : α → β → γ



class MulAction (M : Type u) (α : Type v) extends LAction M α α

class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α


class Mul (M : Type u) extends LAction M M M


infixl:65 " * " => LAction.mul
postfix:max "⁻¹" => Inv.inv




class One (α : Type u) where
  one : α

-- instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
--   ofNat := ‹One α›.1

-- instance (priority := 20) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
--   one := 1



/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, one * a = a
  mul_one : ∀ a : M, a * one = a


/-- A semigroup is a type with an associative `(*)`. -/
class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c)



class Monoid (M : Type u) extends Semigroup M, MulOneClass M



class Group (G : Type u) extends Monoid G, Inv G where
  inv_mul_cancel : ∀ a : G, a⁻¹ * a = one
  mul_inv_cancel : ∀ a : G, a * a⁻¹ = one




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







/-- `MulMemClass S M` says `S` is a type of sets `s : Set M` that are closed under `(*)` -/
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] : Prop where
  /-- A substructure satisfying `MulMemClass` is closed under multiplication. -/
  mul_mem : ∀ {s : S} {a b : M}, a ∈ s → b ∈ s → a * b ∈ s

/-- `OneMemClass S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type*) (M : Type*) [One M] [SetLike S M] : Prop where
  /-- By definition, if we have `OneMemClass S M`, we have `1 ∈ s` for all `s : S`. -/
  one_mem : ∀ s : S, (one : M) ∈ s


/-- `SubmonoidClass S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
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
  mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier


/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type u) [MulOneClass M] extends Subsemigroup M where
  /-- A submonoid contains `1`. -/
  one_mem' : (one : M) ∈ carrier


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
  one_mem := Submonoid.one_mem
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



section sectionProduct

variable (G : Type u) [Group G]

def ProductOfSubgroups (H K : Subgroup G) := {g : G | ∃ h k, h ∈ H.carrier ∧ k ∈ K.carrier ∧ g = h * k}


end sectionProduct






section sectionAction



variable (G : Type u) [Group G] (S : Type u)

class GroupAction extends LAction G S S where
  one_id : ∀ s : S, (one : G) * s = s
  assoc : ∀ (g h : G) (s : S), (g * h) * s = g * (h * s)





def orbit {S G : Type u} [Group G] (s : S) (act : GroupAction G S)  :=
  Set.range fun g : G => act.mul g s


def stabilizer {S G : Type u} [Group G] (s : S) (act : GroupAction G S) : Subgroup G where
  carrier := { m | act.mul m s = s }
  one_mem' := act.one_id s
  mul_mem' {m m'} (ha : act.mul m s = s) (hb : act.mul m' s = s) :=
    show act.mul (m * m') s = s by rw [act.assoc, hb, ha]
  inv_mem' {m} (h : act.mul m s = s) :=
    show act.mul m⁻¹ s = s by sorry


instance (F : Fintype u) : Fintype (orbit G F) := by sorry


def isTransitive (act : GroupAction G S) : Prop := ∀ (s1 s2 : S), ∃ (g : G), act.mul g s1 = s2


theorem orbit_theorem (act : GroupAction G S) : ∀ (x : S), Nat.card G = Nat.mul (Nat.card (orbit x act)) (Nat.card (stabilizer x act)) := by sorry


theorem lagrange (G : Type u) [Group G] (H : Subgroup G) : Nat.card H ∣ Nat.card G := by sorry


end sectionAction










variable (p : ℕ) (G : Type u) [Group G] [Finite G]

def IsPGroup (p : ℕ) (α : Type u) : Prop := ∃ n : ℕ, Nat.card α = p ^ n


def isHighestPowerOfP (n p r : Nat) : Prop := p^r ∣ n ∧ ¬ p^(r+1) ∣ n




variable (p : ℕ) (G : Type u) (pp : Prime p) [Group G] [Finite G] (r : ℕ) (h : isHighestPowerOfP (Nat.card G) p r) (m : ℕ) (h2 : Nat.card G = Nat.mul (p^r) m)

class Sylow extends Subgroup G where
  order : ∃ r : ℕ, Nat.card carrier = p ^ r ∧ isHighestPowerOfP (Nat.card G) p r


def alpha_g (g : G) (h : G) : G := (g * h) * g⁻¹

instance alpha : GroupAction G (Sylow p G) := by sorry
  -- mul := fun (g : G) (S : Sylow p G) => {y : G | ∃ s, s ∈ S.carrier ∧ (alpha_g g s) = y }
  -- one_id :
  -- assoc :




theorem orbit_alpha_divides_m (Q : Sylow p G) : Nat.card (orbit Q (alpha p G)) ∣ m := by sorry



variable (U : Subgroup G) [Group U] (isp : IsPGroup p U)

def Q : Sylow p G := by sorry




instance beta : GroupAction U (orbit (Q p G) (alpha p G)) := by sorry

theorem card_eq_one_or_p_divides (Q P : Sylow p G) (h : P ∈ (orbit Q (alpha p G))) :
(Nat.card (orbit P (beta p G U)) = 1) ∨ (p ∣ (orbit U (orbit G (Sylow p G) Q) U)) := by sorry


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
