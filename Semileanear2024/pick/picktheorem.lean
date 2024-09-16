------------------------------------------------------------------------------
-- Formalizing Pick's Theorem... and learning LEAN along the way.
-- Pick's theorem for closed integer polygons, not necessarily simple
-- This is the algebraic half of Pick's theorem,
-- the umlaufsatz being the geometric other half
------------------------------------------------------------------------------

import Semileanear2024.pick.polygon

------------------------------------------------------------------------------
-- Pick's theorem states (in its algebraic form) that for any lattice polygon
-- the enclosed area equals the number of enclosed lattice points.

example square.area = 4

 ∧ square.nelp = 4 := by
  simp

#eval diamond.area  -- 2
#eval diamond.nelp  -- 2

#eval eight.area  -- 2
#eval eight.nelp  -- 2

theorem area_eq_nelp : ∀ p : Polygon, p.isInteger → p.area = p.nelp := by
  sorry
