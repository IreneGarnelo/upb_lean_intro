import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 4

Title "Aussagen negieren"

Introduction "In diesem Level werden wir lernen, wie wir ein Beweisziel, welches mit einem
Negationszeichen anfängt weiter vereinfacht. In deisem Level zum Beispiel ist
das Beweisziel `¬ a > 4`. Wir wissen, dass das equivalent zu `a ≤ 4` ist. Damit
LEAN diese Umformung macht verwenden wir die Tactic `push_neg,`. Probier es zu
Beginn dieses Beweises aus.

Sei $a in mathbb{N}$ mit $aleq4$. Dann gilt nicht, dass $a>4$.
"

Statement (a : Nat) (h : a ≤ 4) : ¬ a > 4 := by
  push_neg
  exact h
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
