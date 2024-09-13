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

def EmptyRel : Empty → Empty → Prop := fun _ _ ↦ True

instance : IsTrichotomous Empty EmptyRel := sorry
instance : IsTrans Empty EmptyRel := sorry
instance : IsWellFounded Empty EmptyRel := sorry
instance woEmpty : IsWellOrder Empty EmptyRel where

def WellOrderOnEmpty : WellOrder :=
{
  α := Empty
  r := EmptyRel
  wo := woEmpty
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
  r := fun a b ↦ (a < b)
  wo := sorry
}

--if we wish we can reprove the relevant lemmas.
instance : IsTrichotomous ℕ Nat.lt := ⟨Nat.lt_trichotomy⟩
instance : IsTrans ℕ Nat.lt := ⟨@Nat.lt_trans⟩
instance : IsWellFounded ℕ Nat.lt := ⟨Nat.lt_wfRel.wf⟩
instance woNat : IsWellOrder ℕ Nat.lt where

def WellOrderOmega : WellOrder :=
{
  α := ℕ
  r := Nat.lt
  wo := woNat
}

open NatAndAnother

inductive lt (n : NatAndAnother) : NatAndAnother → Prop
  | aright : lt n another
  | step {m} (hm : m ≠ another) : lt n m → lt n (succ m hm)
--is this right?

def WellOrderOmegaPlus1 : WellOrder :=
{
  α := NatAndAnother
  r := lt
  wo := sorry
}

def omega := Ordinal.type WellOrderOmega.r

example : Ordinal.type WellOrderOmegaPlus1.r = omega + 1 := sorry
