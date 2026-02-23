import Game.Metadata

World "Vergleiche"
Level 2

Title "Hinweis-Typen"

Introduction "Statischer Text zu Beginn des Beweises."

Statement (x y z : Nat) (h : x = 2) (g: y = 4)(f: 2 = z) : x + x = y := by
  Hint "Text vor dem ersten Beweisschritt"
  Hint (hidden := true) "Verdeckter Hinweis"
  Branch
    rw [g]
    Hint "Angepasster Text: Falls user `rw[g]` schreibt"
    rw [h]
  rw [h]
  Hint "Angepasster Text: Falls user `rw[h]` schreibt"
  Branch
    rw [f]
    Hint "Hinweis zu nicht zielführendem Beweisschritt"
    sorry
  rw [g]

Conclusion "Text der zu Beweisende auftaucht"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
