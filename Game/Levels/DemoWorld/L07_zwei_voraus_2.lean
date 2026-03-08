import Game.Metadata

World "DemoWorld"
Level 7

Title "Zwei Voraussetzungen - Teil 2"

Introduction "Wir haben nun fast die gleiche Aufgabe wie zuvor. Der einzige Unterschied ist,
dass die beiden Voraussetzungen des Satzes mit einem und-Operator zu einer
Voraussetzung zusammengefasst wurden. In solchen Fällen muss man, wenn man
die Voraussetzung anwenden möchte, spezifizieren welchen Teil davon man meint.
Wenn man die Aussage, die links vom und-Operator ist verwenden möchte schreibt man
`rw h.left,` und ansonsten `rw h.right,`.

Seien $x$ und $y \\in \\mathbb{N}$ mit $x=2$ und $y=3$. Dann ist $x + 1= y$.
"

Statement (x y : Nat)(h: x=2 ∧ y=3) : x+1=y := by
  rw [h.left]
  rw [h.right]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
