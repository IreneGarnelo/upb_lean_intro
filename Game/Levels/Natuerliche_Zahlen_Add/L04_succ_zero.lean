import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 4

Title "Addition mit dem Nachfolger von 0"

Introduction "In diesem Level werden wir zeigen, dass Addition mit dem Nachfolger von $0$ (den
wir noch nicht formal als $1$ eingeführt haben), gleich dem Nachfolger der Zahl ist.
Löse den Beweis mit `rw` und den verfügbaren Axiomen.

Sei $a in mathbb{N}$. Dann ist $a+$`succ`$(0)=$`succ`$(a)$
"

Statement (a : Nat) : a + succ zero = succ a := by
  rw [add_succ]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
