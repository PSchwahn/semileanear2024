------------------------------------------------------------------------------
-- Formalizing Pick's Theorem... and learning LEAN along the way!
-- Pick's theorem for closed integer polygons, not necessarily simple
------------------------------------------------------------------------------

import Semileanear2024.pick.polygon

------------------------------------------------------------------------------
-- Finally, we can state Pick's theorem (in its algebraic form)

theorem area_eq_nelp : ∀ p : Polygon, p.isInteger → p.area = p.nelp := by
  sorry
