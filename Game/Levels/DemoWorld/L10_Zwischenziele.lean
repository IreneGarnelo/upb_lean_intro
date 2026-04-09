import Game.Metadata

World "DemoWorld"
Level 10
TheoremTab "NatZahl"

Title "Zwischenziele mit `have` setzen"

Introduction "Manchmal ist es sinnvoll in Lean sich Aussagen als Zwischenziel zu
setzen die man innerhalb des Beweises zeigt um sie dann im restlichen
Beweis zu verwenden. Das kann man mit der Taktik `have`, die wir bereits
zum Aufteilen von und-Aussagen kennegelernt haben, machen. Übergreifend kann man
sagen, dass `have` neue Aussagen einführt, die man dann zu Beweisen hat.
Im Fall der und-Aussagen ist der Beweis trivialerweise durch die und-Aussage
gegeben.

In dieser Aufgabe möchten wir zeigen, dass für natürliche
Zahlen $a,b,c$ gilt, dass $(a + b) \\cdot c = b \\cdot c + a \\cdot c$.
Statt direkt mit diesem Ziel zu beginnen können wir uns als erstes
vornehmen, das Kommutativgesetzt in diser Variante zu zeigen:
```
 have h : (a + b) * c = a * c + b * c := by
  sorry
```

# `sorry` Keywort
Sorry ist ein Keyword, was so viel bedeutet wie: 'Hier fehlt ein Teil des Beweises'.
Du kannst dieses Keyword verwenden, wenn ein Beweis überprüft werden soll, bei dem
dir noch ein Teil fehlt. LEAN wird bestätigen, dass der Beweis stimmt, in dem er No goals
ausgibt, das aber nicht Level complete steht weist darauf hin, dass noch etwas zu tun ist.

In dieser Aufgabe muss das sorry später noch mit dem Beweis für die Aussage `h` ersetzt werden,
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

NewTactic «sorry»
NewTheorem Nat.add_comm Nat.mul_comm Nat.mul_add
-- NewDefinition Nat Add Eq
