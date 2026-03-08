import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 8

Title "Addition mit dem Nachfolger - von links"

Introduction "Genauso wie wir aus $a+0=a$ nicht direkt $0+a=a$ folgern könnten, können wir
aus $b + $`succ`$(a) =$ `succ`$(b+a)$ nicht `succ`$(a)+b =$ `succ`$(a+b)$
folgern. Wir haben nämlich noch nicht bewiesen, dass die Addition kommutativ ist.

Auch hier können wir einen Induktionsbeweis führen. In diesem Level wirst du einen
unvollständigen Beweis vervollständigen.

Kopiere dazu folgenden unvollständigen Beweis in die Aufgabe:
```
induction b with d hd,
  {rw [add_zero],
  rw [add_zero],},
  {sorry,},
```
Klicke dich durch den Beweis und achte dabei auf den Beweiszustand und wie er sich
mit den unterschiedlichen Beweisschritten ändert. Zu ergänzen ist der Induktionsschritt,
der zurzeit noch durch `sorry,` platzhaltend 'gelöst' ist.

Lösche dieses `sorry,` und ergänze den Induktionsschritt.

Seien $a, b in mathbb{N}$. Dann ist `succ`$(a)+b = $`succ`$(a+b)$.
"

Statement (a b: Nat) : succ a + b = succ (a + b) := by
  induction b
  · rw [Nat.add_zero]
  · rw [add_succ]
    rw [a_1]
    rw [add_succ]

Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
