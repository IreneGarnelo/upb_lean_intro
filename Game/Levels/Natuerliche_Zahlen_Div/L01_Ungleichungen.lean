import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 1

Title "Ungleichungen"

Introduction "Nun werden wir uns mit Ungleichungen auseinandersetzen. Dazu wird als erstes $≤$
definiert. Und zwar ist für natürliche Zahlen $a$ und $b$ genau dann $a≤b$, wenn es
eine natürliche Zahl $c$ gibt, sodass $b=a+c$. Dieser Zusammenhang ist in LEAN
unter dem Satz `le_iff_exists_add` (`le` steht für 'less or equal') gespeichert:

`le_iff_exists_add (a b : ℕ) : a ≤ b ↔ ∃ (c : ℕ), b = a + c`.

Du kannst diesen Satz mit `rw` verwenden. Oft ist es aber sehr aufwändig eine
Ungleichung über die Existenz eines `c` zu zeigen. Deswegen führen wir hier die
Tactic `simp` ein. `simp` verwendet Gleichungen und Ungleichungen im Beweiszustand
um den Beweis zu vereinfachen oder zu beenden. Insbesondere kann `simp` ein
Beweisziel wie `2≤6` lösen.

In diesem Level ist zu zeigen, dass es eine natürliche Zahl kleiner gleich $2$
gibt. Beginne den Beweis, und sobal du ein Beweisziel der Form `a≤b` hast, verwende
`simp`.

Es gibt ein $a in mathbb{N}$ mit $aleq2$.
"

Statement : ∃ a : Nat, a ≤ 2 := by
  use 1
  simp
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
