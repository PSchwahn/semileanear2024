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

theorem orbit_bijection (act : GroupAction G S) (x : S) :
  ∃ (f : Prod (stabilizer x act) (orbit x act) → G), Bijective f := by
    let t := fun ( y : orbit x act ) ↦ y.2.choose -- group element g with g x = y
    let f := fun ( p : Prod (stabilizer x act) (orbit x act) ) ↦ group.mul p.1 (t p.2)
    use f

    -- have h1 : ∀ a : G, ∃ y : orbit x act, y.1 = act.mul a x ∧ y.2 = ⟨ a, rfl ⟩

    -- let g0 := fun ( a : G ) ↦ act.mul a x -- , ⟨ a, rfl ⟩ ⟩

    -- let g := fun ( a : G ) ↦ ⟨ group.mul ( t ⟨ act.mul a x, ⟨ a, rfl ⟩ ⟩ ) a, act.mul a x ⟩

    have inj : Injective f := by sorry
    have sur : Surjective f := by sorry
    exact ⟨ inj, sur ⟩

theorem orbit_formula (act : GroupAction G S) : ∀ (x : S),
  Nat.card G = Nat.card (stabilizer x act) * Nat.card (orbit x act) := by
  intro x

theorem lagrange (G : Type u) [Group G] (H : Subgroup G) :
  Nat.card H ∣ Nat.card G := by sorry


end sectionAction

end Semileanear
