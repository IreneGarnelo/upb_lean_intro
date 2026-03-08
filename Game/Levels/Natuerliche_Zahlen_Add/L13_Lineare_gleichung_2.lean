import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 13

Title "Lösung einer linearen Gleichung mit Zwischenschritt"

Introduction "Hier hast du eine weitere lineare Gleichung $a+2=4$. Als Beweisziel ist aber
nicht der Wert von $a$ gesucht, sonder von $a+3$. Das schafft zwar `linarith`
auch direkt (probier es gerne aus!), wir wollen aber die Gelegenheit nutzen
um zu erklären, wie man sich in Beweisen Zwischenziele setzen kann.

In diesem Beweis könnte es zum Beispiel sinnvoll sein, die Aussage `ha : a=2`
zu beweisen und diese zu verwenden, um `a` mit `rw [ha],` in das Beweisziel einzusetzen.
Um sich eine Aussage als Zwischenziel vorzunehmen verwendet man die Tactic `have`.
Dazu schreibt man:
```
have ha : a = 2,
{...},
```
Man führt die Aussage ha ein, die im weiterem Verlauf verwendet werden kann. Dazu muss
sie aber in den Klammern bewiesen werden.

In diesem Level könnte der Beweis dann so aussehen:
```
have ha : a = 2,
{sorry,}, -- Beweise ha, du kannst dazu linarith verwenden
sorry,    -- Beweise nun mithilfe von ha das Beweisziel
```
Kopiere diesen Code und ergänze die beiden sorry.

Sei $a in mathbb{N}$ mit $a+2=4$. Dann ist $a + 3=5$.
"

Statement (a : Nat) (h : a + 2 = 4): a + 3 = 5 := by
  have ha : a = 2 := by
    linarith
  rw [ha]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
