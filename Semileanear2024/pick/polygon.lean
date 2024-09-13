import Mathlib
-- import Mathlib.Data.Real.Basic
-- import algebra.big_operators.basic
-- import data.nat.interval

------------------------------------------------------------------------------
-- rational points in the plane

@[ext]
structure Point where -- structure or class?
  x : Rat             -- Rat or Int?
  y : Rat             -- Rat or Int?
  deriving Repr       -- enables #eval for debugging

#check Point    -- Type
#check Point.x  -- Int
#check Point.y  -- Int

def p0 : Point where
  x := -3
  y :=  2

#check p0  -- Point
#eval p0   -- { x := -3, y := 2 }

def p1 : Point := ⟨ 5, 3 ⟩
def p2 : Point := ⟨ -1, 7 ⟩

#check p1  -- Point
#check p2  -- Point
#eval p1   -- { x := 5, y := 3 }
#eval p2   -- { x := -1, y := 7 }

def Point.add (u v : Point) : Point := ⟨ u.x + v.x, u.y + v.y ⟩
def Point.sub (u v : Point) : Point := ⟨ u.x - v.x, u.y - v.y ⟩
def Point.cross (u v : Point) : Rat := u.x * v.y - u.y * v.x
def Point.sprod (u v : Point) : Rat := u.x * v.x + u.y * v.y

#check Point.add p0 p1 -- p.add q : Point
#check p0.add p1       -- p.add q : Point
#check p0.add          -- Point → Point
#eval p0.add p1        -- { x := 2, y := 5 }

infixl:65 " + " => Point.add    -- left associative, precedence 65
infixl:65 " - " => Point.sub    -- left associative, precedence 65
infix:70 " × " => Point.cross   -- precedence 70
infix:70 " ⬝ " => Point.sprod   -- precedence 70

#eval p0     -- { x := -3, y := 2 }
#eval p1     -- { x := 5, y := 3 }
#eval p0 + p1  -- { x := 2, y := 5 }
#eval p0 - p1  -- { x := -8, y := -1 }
#eval p0 × p1  -- -19
#eval p0 ⬝ p1  -- -9

------------------------------------------------------------------------------
-- Cast ℤ to ℚ, conversely check whether a:ℚ is an integer by a.den = 1

def x := (1:ℚ)*4/6
#check x     -- ℚ
#eval x      -- (2 : Rat)/3
#eval x.num  -- 2
#eval x.den  -- 3

def Rat.fraction (a b : Int) := (a:ℚ)/(b:ℚ)
infixl:70 " /: " => Rat.fraction

def y := 15/:3
#check y
#eval y
#eval y.num
#eval y.den

def Point.isInteger (q: Point) : Bool :=
  q.x.den = 1 ∧ q.y.den = 1

#eval p0.x.den = 1 ∧ p0.y.den = 1
#eval p0.isInteger

------------------------------------------------------------------------------
-- An array is a list with additional nice features

def l := [7, 8, 9] -- list
#check l      -- List ℕ
#eval l.size  -- invalid field 'size'

def a := #[7, 8, 9] -- array
#check a      -- Array ℕ
#eval a.size  -- 3
#eval a[0]    -- 7
#eval a[1]    -- 8
#eval a[2]    -- 9
#eval a[3]    -- failed to prove that index is valid

#eval a[(2 : Fin 3)] -- 9
#eval a[(3 : Fin 3)] -- 7
#eval a[(4 : Fin 3)] -- 8

------------------------------------------------------------------------------
-- an polygon p = [p_1, ..., p_n] is an array of points

def p : Array Point := #[p0, p1, p2]
#check p     -- Array Point
#eval p      -- #[{ x := -3, y := 2 }, { x := 5, y := 3 }, { x := -1, y := 7 }]
#eval p.size -- 3
#eval p[0]   -- { x := -3, y := 2 }
#eval p[1]   -- { x := 5, y := 3 }
#eval p[2]   -- { x := -1, y := 7 }
#eval p[(3 : Fin 3)]

def isInteger (p: Array Point) : Bool :=
  ∀ i : Fin p.size, p[i].x.den = 1 ∧ p[i].y.den = 1

#eval isInteger p  -- true

def q : Array Point := #[p0, p1, p2, ⟨ 5/:2, 3 ⟩]

#eval isInteger q  -- false
