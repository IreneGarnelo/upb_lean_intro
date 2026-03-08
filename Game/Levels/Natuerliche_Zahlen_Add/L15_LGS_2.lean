import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 15

Title "Lineares Gleichungssystem - Teil 2"

Introduction "In diesem Level möchten wir ein letztes Gleichungssystem lösen.
```
a+b+3=8
a=b+1
```
Es soll gezeigt werden, dass die Lösung
```
a=3
b=2
```
ist. In diesem Fall können wir nicht linarith direkt anwenden, weil in
unserem Beweisziel ein 'und' (`∧`) ist. Man kann aber ein Ziel, welches
ein 'und' (`∧`) enthält mit der Tactic `split` in zwei Unterziele einteilen.
In unserem Fall wird mit `split,` das Ziel `a=3 ∧ b=2` zu den Zielen
`a=3` und `b=2`. Wie beim Induktionsbeweis kannst du die beiden Ziele
in getrennten Umgebungen mit Klammern {} einteilen. Das Gerüst für diesen
Beweis ist also
```
split,
{sorry,},
{sorry,},
```
Kopiere dieses Gerüst, schau dir an was der erste Schritt bewirkt und
ersetze dann die beiden `sorry` mit Beweisen.

Seien $a, b in mathbb{N}$ mit $a+b+3=8$ und $a=b+1$. Dann ist $a=3$ und $b=2$.
"

Statement (a b : Nat) (h : a+b+3=8 ∧ a=b+1) : a=3 ∧ b=2 := by
  constructor
  · linarith [h.1, h.2]
  · linarith [h.1, h.2]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
