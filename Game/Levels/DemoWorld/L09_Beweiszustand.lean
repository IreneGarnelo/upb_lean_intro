import Game.Metadata

World "DemoWorld"
Level 9

Title "`rw` auf Aussagen im Beweiszustand"

Introduction "Wir möchten nun eine neue Eigenschaft der Taktik `rw` einführen. Man kann `rw` auch auf
gegebene Aussagen aus dem Beweiszustand anwenden statt auf das Beweisziel. Man gibt dazu
mit `at NameAussage` an, auf welche Aussage `rw` angewandt werden soll.

In dieser Aufgabe starten wir mit folgendem Beweiszustand:
```
xy: ℕ
h1: x = 2
h2: y = x + 1
⊢ y = 3
```
Um `h1` in `h2` einzusetzen, können wir `rw h1 at h2,` schreiben. Das Beweisziel wird
dadurch nicht geändert, aber `h2` wird zu `h2 : y = 2 + 1`. Probiere es in der Aufgabe aus.

Seien $x$ und $y \\in \\mathbb{N}$ mit $x=2$ und $y=x+1$. Dann ist $y=3$.
"

Statement (x y : Nat)(h1: x=2)(h2 : y=x+1) : y=3 := by
  rw [h1] at h2
  exact h2
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
