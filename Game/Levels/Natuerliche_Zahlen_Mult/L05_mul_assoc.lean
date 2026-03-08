import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Mult"
Level 5

Title "Assoziativität der Multiplikation"

Introduction "Zuletzt Beweisen wir die Assoziativität der Multiplikation. Schau dir dazu zunächst
wieder den Beweis der Assoziativität der Addition an:
```
induction c with d hd,
{repeat{rw [add_zero],},},
{repeat{rw [add_succ],},
rw [hd],},
```
Kannst du auch bei der Assoziativität den Beweis aus der Addition einfach übernehmen?

Seien $a, b, c \\in \\mathbb{N}$. Dann ist $(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)$.
"

Statement (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c
  · repeat rw [mul_zero]
  · repeat rw [mul_succ]
    rw [left_distrib]
    rw [a_1]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
