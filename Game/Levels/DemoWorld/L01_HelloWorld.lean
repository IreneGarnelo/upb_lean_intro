import Game.Metadata

World "DemoWorld"
Level 1

Title "Umformungen in Lean"

Introduction "In diesem Level werden wir ein paar Grundlegende Eigenschaften
von Lean kennenlernen. TODO: Details"

Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "Um dem Ziel näher zu kommen kannst du zuerst entweder den Wert von
  `{x}` (indem du die Aussage `{h}` anwendest) oder von `{y}` (indem du die
  Aussage `{g}` anwendest) einsetzen. Du kannst auch beide Wege probieren. Achte
  dabei darauf, wie sich der Beweiszustand dabei ändert."
  Branch
    rw [g]
    Hint "Jetzt musst du nur noch `{x}` einsetzen."
    rw [h]
  rw [h]
  Hint "Jetzt musst du nur noch `{y}` einsetzen."
  rw [g]

Conclusion "Geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
