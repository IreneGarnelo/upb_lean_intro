import Game.Metadata

World "Koerper"
Level 2

Title "Eindeutigkeit der Multiplikation"

Introduction "Wir werden nun den Beweis führen, dass Multiplikation in Körpern eindeutig ist.
Dieser Beweis wird bis auf ein paar Sonderheiten genauso funktionieren wie die
Eindeutigkeit der Verknüpfung über Gruppen, hier ist der Beweis zur Erinnerung:
```
intro h,
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z),
  { rw h, },
  rw [←mul_assoc, ←mul_assoc] at h_inv,
  rw mul_left_inv x at h_inv,
  repeat{ rw one_mul at h_inv, },
  exact h_inv,
```
Statt `mul_left_inv` heißt es in Körpern aber `mul_inv_cancel`.

Die Multiplikation in Körpern ist eindeutig.
"

Statement {F : Type} [Field F] (x y z : F) (hx : x ≠ 0) :
x * y = x * z → y = z := by
  intro h
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z) := by -- Multiply both sides by x⁻¹
    rw [h]
  rw [←mul_assoc, ←mul_assoc] at h_inv -- Simplify the left-hand and right-hand side
  repeat rw [mul_comm x⁻¹ x] at h_inv
  rw [mul_inv_cancel₀ hx] at h_inv
  repeat rw [one_mul] at h_inv
  exact h_inv
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
