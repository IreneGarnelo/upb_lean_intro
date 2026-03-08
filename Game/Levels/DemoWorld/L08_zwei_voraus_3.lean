import Game.Metadata

World "DemoWorld"
Level 8

Title "Zwei Voraussetzungen - Teil 3"

Introduction "Wir haben die exakte Aufgabe wie zuvor, möchten aber nun sehen, dass wir den
beiden Aussagen, die mit einem und-Operator verbunden wurden, Namen geben können
um diese wieder einzeln verweden zu können. Das lohnt sich insbesondere wenn man
in einem Beweis die Teilaussagen öfter braucht. Dazu verwendet man `have` wiefolgt: <br>
`have h1 := h.left`. Statt `h1` kann man einen beliebigen Namen wählen.

Führe in der unteren Aufgabe die Aussagen `h1` und `h2` ein und benutze sie um den Beweis
mit `rw` zu lösen.

Seien $x$ und $y \\in \\mathbb{N}$ mit $x=2$ und $y=3$. Dann ist $x + 1= y$.
"

Statement (x y : Nat)(h: x=2 ∧ y=3) : x+1=y := by
  have h1 := h.left
  have h2 := h.right
  rw [h1]
  rw [h2]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
