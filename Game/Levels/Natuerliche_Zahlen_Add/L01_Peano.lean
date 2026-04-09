import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 1

Title "Die Peano Axiome"

Introduction "Falls `succ`$(a) = b$, dann `succ`$($`succ`$(a)) = $`succ`$(b)$
"

Statement (a b : Nat) (h : succ a = b): succ (succ a) = succ b := by
  rw [h]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
