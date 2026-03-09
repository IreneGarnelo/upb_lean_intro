import Game.Metadata

World "DemoWorld"
Level 10

Title "Zwischenziele mit `have` setzen"

Introduction "Manchmal ist es sinnvoll in Lean sich Aussagen als Zwischenziel zu
setzen die man innerhalb des Beweises zeigt um sie dann im restlichen
Beweis zu verwenden. Das kann man mit der Taktik `have`, die wir bereits
zum Aufteilen von und-Aussagen kennegelernt haben, machen. Übergreifend kann man
sagen, dass `have` neue Aussagen einführt, die man dann zu Beweisen hat.
Im Fall der und-Aussagen ist der Beweis trivialerweise durch die und-Aussage
gegeben.

In der untenstehenden Aufgabe möchten wir zeigen, dass für natürliche
Zahlen $a,b,c$ gilt, dass $(a + b) \\cdot c = b \\cdot c + a \\cdot c$.
Statt direkt mit diesem Ziel zu beginnen können wir uns als erstes
vornehmen, das Kommutativgesetzt in der Variante, in der die Summanden
vor dem Produkt stehen, zu zeigen. Dazu schreiben wir:
```
 have h : (a + b) * c = a * c + b * c := by
  sorry
```
Das sorry muss nun noch mit dem Beweis für die Aussage `h` ersetzt werden,
die dann im weiterem Verlauf verwendet werden kann.

Du brauchst für diesen Beweis weitere Sätze aus dem Modul `Nat` der
natürlichen Zahlen: `Nat.mul_comm`, `Nat.mul_add` und `Nat.add_comm`.
Schau dir zunächst auf der rechten Spalte an, was diese Sätze aussagen.

Seien $a, b$ und $c \\in \\mathbb{N}$. Dann ist $(a + b) \\cdot c = b \\cdot c + a \\cdot c$.
"

Statement (a b c : Nat) : (a + b) * c = b * c + a * c := by
  have h : (a + b) * c = a * c + b * c := by
    Hint "Wenn du bei einem Satz wie Nat.mul_comm, der zwei Argumente hat,
    festlegen willst, worauf er angewandt werden soll, musst du beide Argumente
    übergeben, in diesem Fall also `rw [Nat.mul_comm (a+b) c]`."
    rw [Nat.mul_comm (a+b) c]
    rw [Nat.mul_add]
    rw [Nat.mul_comm a c]
    rw [Nat.mul_comm c b]
  rw [Nat.add_comm (b*c) (a*c)]
  exact h
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.mul_comm Nat.mul_add
-- NewDefinition Nat Add Eq
