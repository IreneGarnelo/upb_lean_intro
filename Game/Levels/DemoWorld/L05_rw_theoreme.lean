import Game.Metadata

World "DemoWorld"
Level 5

Title "`rw` und gegebene Sätze"

Introduction "Man kann die Taktik `rw` auch in Verknüpfüng mit bekannten Sätze verwenden. In
Lean ist viel der Mathematik mit der wir an der Uni arbeiten implementiert und kann
in Beweisen verwendet werden. In der linken Spalte findest du unter 'Theorem statements'
einiger solche Sätze, die für diese Lernumgebung nützlich sein könnten.

Einer dieser Sätze ist `mul_one` und sagt aus, dass für eine natürliche Zahl
`x` gilt, dass `x*1=x` ist. Wenn man also in einem Beweiszustand `x*1` hat, kann
man das mit `rw mul_one,` vereinfachen. Probiere es in dieser Aufgabe aus.

Sei $x \\in \\mathbb{N}$. Dann ist $x \\cdot 1=x$.
"

Statement (x : Nat) : x*1=x := by
  rw [Nat.mul_one x]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
