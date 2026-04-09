import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 2

Title "Die Peano Axiome - Teil 2"

Introduction "Du kannst das untenstehende Theorem ähnlich wie Level 1 lösen, aber erkennst du
auch einen weiteren Weg der `←` verwendet?

Falls `succ`$(a) = b$ und `succ`$(b)= c$, dann `succ`$($`succ`$(a)) = c$
"

Statement (a b c : Nat) (h : succ a = b) (g : succ b = c): succ (succ a) = c := by
  rw [← g]
  rw [h]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
