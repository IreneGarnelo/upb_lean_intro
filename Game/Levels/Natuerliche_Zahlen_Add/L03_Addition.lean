import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 3

Title "Addition natürlicher Zahlen"

Introduction "Man kann die Addition zweier natürlichen Zahlen rekursiv anhand der Peano-Axiome
definieren.
- Für $a in N$ sei $a+0=a$
- Für $a,d in N$ sei $a+$`succ`$(d) = $`succ`$(a+d)$

Nach dem Prinzip der Induktion ist dann die Addition für alle Paare von natürlichen
Zahlen definiert.

Die beiden Aussagen, die die Addition definieren, sind in LEAN implementiert und
haben jeweils den Namen `add_zero` und `add_succ`.

$a+$`succ`$(0)=$`succ`$(a)$
"

Statement (a : Nat) : succ a + zero  = succ (a + zero) := by
  rw [Nat.add_zero a]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTheorem Nat.add_zero
-- NewDefinition Nat Add Eq
