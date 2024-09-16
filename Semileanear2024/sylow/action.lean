import Semileanear2024.sylow.basic

namespace Semileanear

section sectionAction

variable (G : Type u) [group : Group G] (S : Type u)

class GroupAction extends LAction G S S where
  one_id : ∀ s : S, (one : G) ~ s = s
  assoc : ∀ (g h : G) (s : S), (g ~ h) ~ s = g ~ (h ~ s)

--def orbit {S G : Type u} [Group G] (s : S) (act : GroupAction G S)  :=
--  Set.range fun g : G => act.mul g s

def orbit {S G : Type u} [Group G] (x : S) (act : GroupAction G S)  :=
  { y : S // ∃ (g : G), act.mul g x = y }

def stabilizer {S G : Type u} [Group G] (s : S) (act : GroupAction G S) : Subgroup G where
  carrier := { m | act.mul m s = s }
  one_mem' := act.one_id s
  mul_mem' {m m'} (ha : act.mul m s = s) (hb : act.mul m' s = s) :=
    show act.mul (m ~ m') s = s by rw [act.assoc, hb, ha]
  inv_mem' {m} (h : act.mul m s = s) :=
    show act.mul m⁻¹ s = s by nth_rewrite 1 [← h, ← act.assoc, act.one_id ]; rfl

instance (S: Type u) (F : Finset S) (f : F) (act : GroupAction G F): Finset (orbit f act) := by sorry

def isTransitive (act : GroupAction G S) : Prop := ∀ (s1 s2 : S), ∃ (g : G), act.mul g s1 = s2

open Function

theorem orbit_formula (act : GroupAction G S) : ∀ (x : S),
  Nat.card G = Nat.card (stabilizer x act) * Nat.card (orbit x act) := by
  sorry

theorem orbit_bijection (act : GroupAction G S) (x : S) :
  ∃ (f : Prod (orbit x act) (stabilizer x act) → G), Bijective f := by

    let toOrb (a : G) : orbit x act := ⟨ act.mul a x, by use a ⟩

    have toOrbSur : Surjective toOrb := by
      intro y
      simp [toOrb]
      obtain ⟨ g, hg ⟩ := y.2
      use g
      apply Subtype.ext; simp; exact hg

    have exists_rinv : HasRightInverse toOrb := by
      rw [← surjective_iff_hasRightInverse ]
      exact toOrbSur
    obtain ⟨ toGrp, htoGrp ⟩ := exists_rinv

    let f ( p : Prod (orbit x act) (stabilizer x act) ) := group.mul (toGrp p.1) p.2
    use f

    let toStb (a : G) : (stabilizer x act) :=
      ⟨ group.mul (toGrp (toOrb a))⁻¹ a, by apply GroupAction.one_id x ⟩
    let finv (a : G) : Prod (orbit x act) (stabilizer x act) :=
      ⟨ toOrb a, toStb a ⟩

    rw [bijective_iff_has_inverse]
    use finv

    constructor
    intro ⟨ y, a ⟩
    simp [f, finv]

    constructor
    simp [toOrb]

theorem lagrange (G : Type u) [Group G] (H : Subgroup G) :
  Nat.card H ∣ Nat.card G -- :=  by
  := ⟨ H.index, mul_comm H.index _ ▶ H.index_mul_card.symm ⟩
  sorry

end sectionAction

end Semileanear
