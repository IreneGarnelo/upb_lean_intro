import Game.Metadata

World "DemoWorld"
Level 6

Title "Zwei Voraussetzungen - Teil 1"

Introduction "In der folgenden Aufgabe gibt es zwei Voraussetzungen. Benutze beide
zusammen mit `rw` um die Aufgabe zu lösen.
"

Statement (x y : Nat)(h1: x=2)(h2 : y=3) : x+1=y := by
  rw [h1]
  rw [h2]
Conclusion "Beweis geschafft!"

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
