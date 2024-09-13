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

instance woEmpty : IsWellOrder Empty EmptyRel where
  trichotomous := sorry
  trans := sorry
  wf := sorry

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
instance woNat : IsWellOrder ℕ Nat.lt where
  trichotomous := Nat.lt_trichotomy
  trans := @Nat.lt_trans
  wf := Nat.lt_wfRel.wf

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

instance woNatAndAnother : IsWellOrder NatAndAnother lt where
  trichotomous := sorry
  trans := sorry
  wf := sorry

def WellOrderOmegaPlus1 : WellOrder :=
{
  α := NatAndAnother
  r := lt
  wo := woNatAndAnother
}

def omega := Ordinal.type WellOrderOmega.r

example : Ordinal.type WellOrderOmegaPlus1.r = omega + 1 := sorry
