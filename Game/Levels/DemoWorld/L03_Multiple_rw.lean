import Game.Metadata

World "DemoWorld"
Level 3

Title "Mehrere Beweisschritte mit `rw`"

Introduction "Wir werden nun einen Beweis bearbeiten, in dem man mehrfach die
`rw` Taktik verwenden muss. Der folgende Satz hat zwei Voraussetzungen. Benutze beide
zusammen mit `rw` um die Aufgabe zu lösen."

Statement (x y : Nat) (h : x = 2) (g: y = 4) : x + x = y := by
  Hint "Um dem Ziel näher zu kommen kannst du zuerst entweder den Wert von
  `{x}` (indem du die Aussage `{h}` anwendest) oder von `{y}` (indem du die
  Aussage `{g}` anwendest) einsetzen. Du kannst auch beide Wege probieren. Achte
  dabei darauf, wie sich der Beweiszustand ändert."
  Branch
    rw [g]
    Hint "Jetzt musst du nur noch `{x}` einsetzen."
    rw [h]
  rw [h]
  Hint "Jetzt musst du nur noch `{y}` einsetzen."
  rw [g]

Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
