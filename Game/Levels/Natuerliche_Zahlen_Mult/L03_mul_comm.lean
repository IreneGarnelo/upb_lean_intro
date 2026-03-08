import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Mult"
Level 3

Title "Kommutativität der Multiplikation"

Introduction "Die Ergebnisse aus Level 1 und 2 sind genug, um die Kommutativität der Multiplikation
zu zeigen! Hier ist zur Erinnerung der Beweis der Kommutativität der Addition:
```
induction b with d hd,
{rw [add_zero a],
rw [zero_add a],},
{rw [add_succ a],
rw [hd],
rw [succ_add d],},
```

Seien $a, b \\in \\mathbb{N}$. Dann ist a ⬝ b = b ⬝ a
"

Statement (a b : Nat) : a * b = b * a := by
  induction b
  · rw [mul_zero]
    rw [zero_mul]
  · rw [mul_succ]
    rw [a_1]
    rw [succ_mul]
Conclusion "Beweis geschafft! Vielleicht ist dir aufgefallen, dass man in dem Beweis aus der Addition nur
überall `add` mit `mul` ersetzten musste. Wie sieht in normaler mathematischen
Sprache aus? Formuliere dazu die Beweise add_comm und mul_comm schriftlich aus."

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
