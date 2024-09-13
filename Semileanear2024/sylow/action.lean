import Semileanear2024.sylow.basic


namespace Semileanear


section sectionAction



variable (G : Type u) [Group G] (S : Type u)

class GroupAction extends LAction G S S where
  one_id : ∀ s : S, (one : G) ~ s = s
  assoc : ∀ (g h : G) (s : S), (g ~ h) ~ s = g ~ (h ~ s)





--def orbit {S G : Type u} [Group G] (s : S) (act : GroupAction G S)  :=
--  Set.range fun g : G => act.mul g s

def orbit {S G : Type u} [Group G] (s : S) (act : GroupAction G S)  :=
  {x : S // ∃ (g : G), act.mul g s = x}


def stabilizer {S G : Type u} [Group G] (s : S) (act : GroupAction G S) : Subgroup G where
  carrier := { m | act.mul m s = s }
  one_mem' := act.one_id s
  mul_mem' {m m'} (ha : act.mul m s = s) (hb : act.mul m' s = s) :=
    show act.mul (m ~ m') s = s by rw [act.assoc, hb, ha]
  inv_mem' {m} (h : act.mul m s = s) :=
    show act.mul m⁻¹ s = s by sorry


instance (S: Type u) (F : Finset S) (f : F) (act : GroupAction G F): Finset (orbit f act) := by sorry


def isTransitive (act : GroupAction G S) : Prop := ∀ (s1 s2 : S), ∃ (g : G), act.mul g s1 = s2


theorem orbit_theorem (act : GroupAction G S) : ∀ (x : S), Nat.card G = Nat.mul (Nat.card (orbit x act)) (Nat.card (stabilizer x act)) := by sorry


theorem lagrange (G : Type u) [Group G] (H : Subgroup G) : Nat.card H ∣ Nat.card G := by sorry


end sectionAction

end Semileanear
