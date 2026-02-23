import Game.Metadata
import Mathlib.Algebra.Group.Basic

World "Vergleiche"
Level 1

Title "Editor mode vs. Typewriter Mode"

Introduction "Editor mode: klassischer Lean-Aufbau.

Typewriter mode: Beweis wird Schritt für Schritt eingegeben,
alle Beweiszustände sind gleichzeitig sichtbar."

Statement {G : Type*} [Group G] (h : ∀ a : G, a⁻¹ = a) :
    ∀ a b : G, a * b = b * a := by
  Hint "`intro a b`"
  intro a b
  Hint "`have h1 : (a * b)⁻¹ = a * b := by rw [h]`"
  have h1 : (a * b)⁻¹ = a * b := by
    {rw [h]}
  Hint "`have h2 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev a b]`"
  have h2 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    {rw [mul_inv_rev a b]}
  Hint "`rw [h1] at h2`"
  rw [h1] at h2
  Hint "`rw [h a] at h2`"
  rw [h a] at h2
  Hint "`rw [h b] at h2`"
  rw [h b] at h2
  Hint "`exact h2`"
  exact h2
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
