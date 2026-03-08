import Game.Metadata

World "Koerper"
Level 5

Title "Kürzen von Brüchen"

Introduction "Zuletz zeigen wir, dass man Brüche kürzen kann. In diesem Beweis reicht es, mit `rw`
zu arbeiten. Suche dir dazu aus der linken Spalte die richtigen Sätze aus.

Für $x, y in F$ mit $y neq 0$ gilt: $frac{x cdot y}{y} = x$.
"

Statement {F : Type} [Field F] (x y : F) (hy : y ≠ 0) : x * y / y = x := by
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  rw [mul_inv_cancel₀ hy]
  rw [mul_one]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
