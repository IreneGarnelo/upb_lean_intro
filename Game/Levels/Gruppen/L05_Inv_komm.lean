import Game.Metadata

World "Gruppen"
Level 5

Title "Falls Inverse kommutieren, dann ist $G$ abelsch"

Introduction "Wir werden uns nun folgendes Lemma anschauen, welches wir in der letzten Aufgabe
anwenden werden. Du musst diesen Beweis nicht selber führen, sondern kannst ihr
einfach mithilfe der Lean-Ausgabe nachvollziehen:
```
intros x y,
specialize h x y,
have h1 : (x⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * x⁻¹)⁻¹, from congr_arg has_inv.inv h,
rw mul_inv_rev x⁻¹ y⁻¹ at h1,
rw mul_inv_rev y⁻¹ x⁻¹ at h1,
repeat {rw inv_inv at h1,},
exact h1.symm,
```
Du musst nicht alle Keywörter wie `specialize` und `congr_arg` kennen. Kannst du
trotzdem für jeden Schritt beschreiben was passiert?

Falls $x^{-1} \\cdot y^{-1} = y^{-1} \\cdot x^{-1}$ für alle $x,y \\in G$, dann ist $G$ abelsch.
"

Statement {G : Type} [Group G]
(h : ∀ x y : G, x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹) :
∀ x y : G, x * y = y * x := by
  intros x y
  specialize h x y
  have h1 : (x⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * x⁻¹)⁻¹ := congrArg Inv.inv h
  rw [mul_inv_rev x⁻¹ y⁻¹] at h1
  rw [mul_inv_rev y⁻¹ x⁻¹] at h1
  rw [inv_inv] at h1
  rw [inv_inv] at h1
  exact h1.symm
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic specialize
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
