------------------------------------------------------------------------------
-- Formalizing Pick's Theorem... and learning LEAN along the way.
-- We formalize the umlaufsatz for simply closed polygons, completing Pick
------------------------------------------------------------------------------

import Semileanear2024.pick.polygon

------------------------------------------------------------------------------
-- A polygon is simple iff ({vertices},open edges) are mutually disjoint

def Polygon.isSimple (p : Polygon) : Bool :=
  sorry

------------------------------------------------------------------------------
-- The umlaufsatz for simply closed polygons -- FIXME orientation?

theorem umlaufsatz : ∀ p : Polygon, p.isSimple → p.umlaufzahl = 1 := by
  sorry
