import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 2

Title "Pythagoreisches Tripel"

Introduction "Ein pythagoreisches Tripel besteht aus drei positiven natürlichen Zahlen $a$, $b$
und $c$, die die Gleichung $a^2 + b^2 = c^2$ erfüllen. Diese Tripel sind besonders
bekannt im Zusammenhang mit dem Satz des Pythagoras, der besagt, dass in einem
rechtwinkligen Dreieck das Quadrat der Länge der Hypotenuse $c$ gleich der Summe der Quadrate
der Längen der beiden Katheten $a$ und $b$ ist.

In diesem Level möchten wir zeigen, dass ein solches Tripel existiert. Da wir keine
Potenzen eingeführt haben schreiben wir $a^2$ als $a⬝a$.

Es gibt $a, b, c in mathbb{N}$ mit $a⬝a+b⬝b+c⬝c$.
"

Statement : ∃ a b c : Nat, a * a + b * b = c * c := by
  use 3, 4, 5
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
