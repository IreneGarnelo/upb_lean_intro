import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Mult"
Level 4

Title "Das Distributivgesetz"

Introduction "Das Distributivgesetz gibt uns an, wie wir mit Ausdrücken umgehen können, in denen
Addition und Multiplikation vorkommen. Wir werden hier die 'Linksdistributivität'
zeigen, also $c⬝(a+b)=c⬝a+c⬝b$, daraus folgt aber nicht direkt $(a+b) ⬝ c=a⬝c+b⬝c$.

In diesem Level startest du den Beweis selber. Wenn du nicht weiterkommst sind
unter der Aufgabe Hinweise.

Seien $a, b, c \\in \\mathbb{N}$. Dann ist $c ⬝ (a + b) = c ⬝ a + c ⬝ b$.
"

Statement (a b c : Nat) : c * (a + b) = c * a + c * b := by
  induction b
  · rw [add_zero]
    rw [mul_zero]
    rw [add_zero]
  · rw [add_succ]
    rw [mul_succ]
    rw [a_1]
    rw [mul_succ]
    rw [add_assoc]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
