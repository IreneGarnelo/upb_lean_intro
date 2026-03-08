import Game.Metadata

World "DemoWorld"
Level 10

Title "Mehrere Beweisschritte mit `rw`"

Introduction "Manchmal ist es sinnvoll in Lean sich Aussagen als Zwischenziel zu
setzen die man innerhalb des Beweises zeigt um sie dann im restlichen
Beweis zu verwenden. Das kann man mit der Taktik `have`, die wir bereits
zum Aufteilen von und-Aussagen kennegelernt haben. Übergreifend kann man
sagen, dass `have` neue Aussagen einführt, die man dann zu Beweisen hat.
Im Fall der und-Aussagen ist der Beweis trivialerweise durch die und-Aussage
gegeben.

In der untenstehenden Aufgabe möchten wir zeigen, dass für natürliche
Zahlen $a,b,c$ gilt, dass $(a + b) \\cdot c = b \\cdot c + a \\cdot c$.
Statt direkt mit diesem Ziel zu beginnen können wir uns als erstes
vornehmen, das Kommutativgesetzt in der Variante, in der die Summanden
vor dem Produkt stehen, zu zeigen. Dazu schreiben wir:
```
 have h : (a + b) * c = a * c + b * c,
  {
  sorry,
  },
```
zwischen den Klammern kommt dann der Beweis für die Aussage `h`, die dann im
weiterem Verlauf verwendet werden kann.

Seien $a, b$ und $c \\in \\mathbb{N}$. Dann ist $(a + b) \\cdot c = b \\cdot c + a \\cdot c$.
"

Statement (a b c : Nat) : (a + b) * c = b * c + a * c := by
  have h : (a + b) * c = a * c + b * c := by
    rw [Nat.mul_comm (a+b) c]
    rw [Nat.mul_add]
    rw [Nat.mul_comm a c]
    rw [Nat.mul_comm c b]
  rw [Nat.add_comm (b*c) (a*c)]
  exact h
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
