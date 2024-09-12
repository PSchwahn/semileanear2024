import Semileanear2024.ordinals.wellorder

/- Exercises:
 Define well-orders on {}, Fin 1, Fin 2, Fin n, Nat, and omega+1
 Make them into ordinals, show that addition works as expected
-/

variable (n : ℕ)

#check Empty
#check Fin n
#check ℕ

open Semileanear2024

#check NatAndAnother

def WellOrderOnEmpty : WellOrder :=
{
  α := Empty
  r := sorry
  wo := sorry
}

def WellOrderOn1 : WellOrder :=
{
  α := Fin 1
  r := sorry
  wo := sorry
}

def WellOrderOn2 : WellOrder :=
{
  α := Fin 2
  r := sorry
  wo := sorry
}

def WellOrderOnFinite : WellOrder :=
{
  α := Fin n
  r := sorry
  wo := sorry
}

def WellOrderOmega : WellOrder :=
{
  α := ℕ
  r := sorry
  wo := sorry
}

def WellOrderOmegaPlus1 : WellOrder :=
{
  α := NatAndAnother
  r := sorry
  wo := sorry
}

#check Ordinal.type WellOrderOnEmpty.r
