import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 11

Title "Ein Existenzbeweis"

Introduction "Nun hast du alle grundlegenden Eigenschaften der Addition gezeigt. In den
verbleibenden Levels der 'Addition' möchten wir nun ein bisschen rechnen.

In diesem Level geht es konkret darum zu zeigen, dass es natürliche Zahlen
$a$ und $b$ gibt, sodass a+b=10. Um das zu beweisen muss man nur ein solches
Paar an Zahlen angeben, zum Beispiel $4$ und $6$. In diesem Level werden wir
die Tactic `use` kennenlernen, mit der man bei Existenzaussagen im Beweisziel
konkrete Objekte übergeben kann. Wir führen `use` am Beispiel dieses Levels ein:
Der Zustand ist:
```
⊢ ∃ (a b : ℕ), a + b = 10
```
Mit `use [4,6],` wird das Beweisziel ersetzt durch `⊢ 4 + 6 = 10`, was den
Beweis direkt löst.
Probier diesen Schritt direkt im Beweis aus. Du kannst $4$ und $6$ nun auch durch
andere Zahlenpaare ersetzen, die $10$ ergeben. Probiere zuletzt noch aus, den
Schritt einzuteilen in:
```
use [4],
use [6],
```
dann kannst du im Zwischenschritt nachvollziehen, was `use` verändert hat.

Für welches $a in mathbb{N}$ kann der Beweis mit `repeat{use [a],},` gelöst werden?
"

Statement : ∃ a b : Nat, a + b = 10 := by
  use 4,6
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
