import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 5

Title "Die Zahl $1$"

Introduction "Aus praktischen Gründen möchten wir nun dem Nachfolger von $0$ einen Namen
geben. Diese Zahl nennen wir $1$ (in Lean `one`). Die Aussage `one = succ(zero)` heißt in
LEAN `one_eq_succ_zero`.

Nun können wir zeigen, dass der Nachfolger von $a$ gleich $a+1$ ist. Löse
den Beweis mit `rw` und den verfügbaren Axiomen `one_eq_succ_zero`,
`add_succ` und `add_zero`.
"

Statement (a : Nat) : succ a = a + 1 := by
  rw [add_succ]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
