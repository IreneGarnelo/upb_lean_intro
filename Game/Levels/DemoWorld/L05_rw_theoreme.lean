import Game.Metadata

World "DemoWorld"
Level 5
TheoremTab "NatZahl"

Title "`rw` und gegebene Sätze"

Introduction "Man kann die Taktik `rw` auch in Verknüpfüng mit bekannten Sätze verwenden. In
Lean ist viel der Mathematik mit der wir an der Uni arbeiten implementiert und kann
in Beweisen verwendet werden. In der linken Spalte findest du unter 'Theorem statements'
einiger solche Sätze, die für diese Lernumgebung nützlich sein könnten.

Einer dieser Sätze ist `Nat.mul_one` und sagt aus, dass für eine natürliche Zahl
`x` gilt, dass `x*1=x` ist. Wenn man also in einem Beweiszustand `x*1` hat, kann
man das mit `rw [Nat.mul_one x]` vereinfachen. Probiere es in dieser Aufgabe aus.

Das 'Nat.' vor dem Satzname gibt an, dass dieser Satz aus dem
Modul der natürlichen Zahlen kommt. Das ist insbesondere bei
Sätzen nötig, die in mehreren Kontexten existieren. In Fall von `mul_one`
gibt es den Satz auch für andere Zahlenbereiche.

Sei $x \\in \\mathbb{N}$. Dann ist $x \\cdot 1=x$.
"

Statement (x : Nat) : x*1=x := by
  Hint "Du brauchst den Satz `Nat.mul_one`."
  rw [Nat.mul_one x]
Conclusion "Beweis geschafft!"


NewTheorem Nat.mul_one
-- NewDefinition Nat Add Eq
