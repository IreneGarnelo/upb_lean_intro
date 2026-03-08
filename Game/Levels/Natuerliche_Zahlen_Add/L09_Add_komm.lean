import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 9

Title "Kommutativität der Addition"

Introduction "Endlich können wir zeigen, dass die Addition kommutativ ist!

Auch hier können wir einen Induktionsbeweis führen. In diesem Level wirst du einen
fast richtigen Beweis korrigieren.

Kopiere dazu folgenden Beweis mit Fehler in die Aufgabe:
```
induction b with d hd,
{rw [add_zero(a)],
rw [zero_add(a)],},
{rw [add_succ(a)],
rw [hd],
rw [succ_add(b)],},
```
Klicke dich durch den Beweis und achte dabei auf den Beweiszustand und wie er sich
mit den unterschiedlichen Beweisschritten ändert. Zu korrigieren ist der Induktionsschritt.

Finde den Fehler, indem du insbesondere auf die Fehlermeldung achtest. Kannst du den Beweis
korrigieren?

Seien $a, b \\in \\mathbb{N}$. Dann ist a+b=b+a.
"

Statement (a b: Nat) : a + b = b + a := by
  Hint (hidden := true) "Der Fehler `unknown identifier 'b'` deutet darauf hin, dass LEAN die Variable `b` in diesem
Kontext nicht kennt. Denk daran, dass im Induktionschritt bewiesen wird, dass falls die
Aussage für ein `d` (also a+d=d+a) gilt, die Aussage auch für `d.succ`
(also a+d.succ = d.succ+a) gilt. Hier kommt also kein `b` mehr vor."
  induction b
  · rw [Nat.add_zero a]
    rw [Nat.zero_add a]
  · rw [add_succ a]
    rw [a_1]
    rw [succ_add n]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
