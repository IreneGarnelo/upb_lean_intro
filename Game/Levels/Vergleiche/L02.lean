import Game.Metadata

World "Vergleiche"
Level 2

Title "Hinweis-Typen"

Introduction "Static Text that appears when the level is loaded."

Statement (x y z : Nat) (h : x = 2) (g: y = 4)(f: 2 = z) : x + x = y := by
  Hint "Text that appears before the student types their first step."
  Hint (hidden := true) "Hidden hint, can be clicked on."
  Branch
    rw [g]
    Hint "Text displayed in case student starts with `rw[g]`."
    rw [h]
  rw [h]
  Hint "Text displayed in case student starts with `rw[h]`."
  Branch
    rw [f]
    Hint "Text displayed in case student uses `rw[f]`, which is not
    helpful here."
    sorry
  rw [g]

Conclusion "Text that appears after the proof is finished."

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
