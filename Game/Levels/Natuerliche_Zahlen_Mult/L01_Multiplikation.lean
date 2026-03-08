import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Mult"
Level 1

Title "Die Multiplikation"

Introduction "Man kann auch die Multiplikation zweier natürlichen Zahlen rekursiv anhand der
Peano-Axiome definieren.
- Für $a in mathbb{N}$ sei $a⬝0=0$
- Für $a,d in mathbb{N}$ sei $a⬝ $`succ`$(d) = a⬝d+a$

Nach dem Prinzip der Induktion ist dann die Multiplikation für alle Paare von
natürlichen Zahlen definiert.

Die beiden Aussagen, die die Multiplikation definieren, sind in LEAN implementiert und
haben jeweils den Namen `mul_zero` und `mul_succ`.

Wir werden in den nächsten Levels wieder grundlegende Rechenregeln beweisen. Dazu werden
wir wieder ohne `linarith` arbeiten.
In diesem level werden wir zeigen, dass auch die Multiplikation mit $0$ von links $0$ ergibt.
Wir haben die Kommutativität der Multiplikation noch nicht gezeigt. Da die Definition
der Multiplikation sehr ähnlich zu der der Addition ist, wird auch dieser Beweis sehr ähnlich
zu dem Beweis $0+a=0$ (Addition - level 4) sein, du kannst diesen als Fahrplan verwenden:
```
induction a with d hd,
{rw [add_zero],},
{rw [add_succ],
rw [hd],},
```

Sei $a in mathbb{N}$. Dann ist $0⬝a=0$.
"

Statement (a: Nat) : zero*a = zero := by
  induction a
  · rw [Nat.mul_zero]
  · rw [mul_succ]
    rw [a_1]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
