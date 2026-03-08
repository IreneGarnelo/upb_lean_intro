import GameServer
-- import Mathlib.Tactic.Common
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-! Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one file Lean file per world
which imports all its levels.
-/

-- theorems that are reused
theorem inv_comm_group_comm {G : Type} [Group G]
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
