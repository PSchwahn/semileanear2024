--You probably want to import Mathlib.
import Mathlib

variable (f : Polynomial ℂ)
variable (z : ℂ)

#check f

theorem fundamental_theorem_of_algebra (hf : f.degree > 0) : ∃ z : ℂ, f.eval z = 0 :=
  Complex.exists_root hf
