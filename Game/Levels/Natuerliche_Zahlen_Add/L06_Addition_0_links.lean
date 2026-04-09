import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 6

Title "Addition"

Introduction "Laut Definition der Addition gilt: $a+0=a$. Wir haben aber noch nicht bewiesen,
dass die Addition kommutativ ist. Es ist also noch nicht bewiesen, dass auch
$0+a=a$ gilt.

Dies werden wir über Induktion zeigen. Dazu lernen wir die `induction` Tactic in
LEAN. Um einen Induktionsbeweis zu starten, müssen wir `induction a with`
schreiben. Dabei ist das $a$ die Variable, über die induziert werden soll.

Nachdem du den Befehl `induction a with` eingibst, wirst du in dem Beweiszustand
sehen, dass du zwei Beweisziele hast: den Induktionsanfang und die
Induktionsvoraussetzung. Um den Beweis übersichtlicher zu führen, kannst du
die zwei Teile wiefolgt strukturieren:
  `induction a with
  | zero =>
  | succ d hd =>

Sei $a in \\mathbb{N}$. Dann ist $0+a=a$.
"

Statement (a : Nat) : zero + a = a := by
  induction a with
  | zero => rw[Nat.add_zero]
  | succ d hd =>
    rw [add_succ]
    rw [hd]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic induction
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
