import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 3

Title "Gerade Quadratzahl"

Introduction "In diesem Level möchten wir zeigen, dass es eine gerade Quadratzahl gibt. Eine
natürliche Zahl $a$ heiß Quadratzahl, genau dann wenn es eine natürliche Zahl
$b$ gibt, sodass $a=c^2$. In diesem Level werden wir das als `a=c⬝c` schreiben.

Es gibt $a, b, c in mathbb{N}$ mit $a=2⬝b$ und $a=c⬝c$.
"

Statement : ∃ a b c : Nat, a = 2 * b ∧ a = c * c := by
  use 16, 8, 4
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
