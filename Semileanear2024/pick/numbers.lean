import Mathlib
-- import Mathlib.Data.Nat.Basic
-- import Mathlib.Data.Int.Basic
-- import Mathlib.Data.Rat.Basic
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Data.Complex.Basic

------------------------------------------------------------------------------
-- The number system, without inclusion, needs cast

#check 0        -- 0 : ℕ
#check (0 : ℕ)  -- 0 : ℕ
#check (0 : ℤ)  -- 0 : ℤ
#check (0 : ℚ)  -- 0 : ℚ
#check (0 : ℝ)  -- 0 : ℝ
#check (0 : ℂ)  -- 0 : ℂ

#check (1 : ℤ) + (2 : ℚ)  -- ℤ
#eval  (1 : ℤ) + (2 : ℚ)  -- 3

------------------------------------------------------------------------------
-- Natural numbers as inductive type

inductive N where
  | zero : N
  | succ : N → N
  deriving Repr  -- enables #eval for debugging

#check N.zero
#check N.succ
#check N.zero.succ
#check N.zero.succ.succ

------------------------------------------------------------------------------
-- Integers as inductive types

inductive Z where
  | ofN : N → Z
  | negSucc : N → Z
  deriving Repr  -- enables #eval for debugging

#check Z.ofN N.zero
#check Z.ofN N.zero.succ
#check Z.ofN N.zero.succ.succ
#check Z.negSucc N.zero
#check Z.negSucc N.zero.succ
#check Z.negSucc N.zero.succ.succ

------------------------------------------------------------------------------
-- Rational numbers ℚ from Mathlib

def x := (1:ℚ)*4/6
#check x     -- ℚ
#eval x      -- (2 : Rat)/3
#eval x.num  -- 2
#eval x.den  -- 3

def Rat.fraction (a b : Int) := (a:ℚ)/(b:ℚ)
infixr:70 " /: " => Rat.fraction
def y := 15/:3
#check y
#eval y
#eval y.num
#eval y.den
