import Game.Metadata
#check inv_mul_eq_one

World "Gruppen"
Level 2

Title "Die Gruppenverknüpfung ist eindeutig"

Introduction "Als nächstes werden wir uns einen längeren Beweis anschauen. Da dieser
aus vielen Schritten besteht ist er vorgegeben, damit du ihn zusammen mit
dem Lean Output nachvollziehen kannst. Der Beweis funktioniert wiefolgt:
```
intro h,
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z),
  { rw h, },
  rw [←mul_assoc, ←mul_assoc] at h_inv,
  rw mul_left_inv x at h_inv,
  repeat{ rw one_mul at h_inv, },
  exact h_inv,
```
Kannst du in Worten beschreiben was in jedem Schritt passiert? In dem Beweis kommt
die neue Taktik `repeat` vor. Kannst du aus dem Kontext erahnen was sie tut?

Die Gruppenverknüpfung ist eindeutig.
"

Statement {G : Type} [Group G] (x y z : G) :
x * y = x * z → y = z := by
  intro h
  have h_inv : x⁻¹ * (x * y) = x⁻¹ * (x * z) := by
    rw [h]
  rw [←mul_assoc, ←mul_assoc] at h_inv
  simp at h_inv
  repeat{ rw [one_mul] at h_inv}
  exact h_inv
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic simp
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
