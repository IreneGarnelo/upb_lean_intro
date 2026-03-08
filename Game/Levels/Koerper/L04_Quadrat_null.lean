import Game.Metadata

World "Koerper"
Level 4

Title "Falls $x^2=0$ dann $x=0$"

Introduction "Aus der vorherigen Aufgabe kann man folgern, dass falls $x^2=0$ dann $x=0$. Du kannst
dazu konkret den Satz, der in Level 3 bewiesen wurde verwenden. Da es in dem Satz
Fälle gibt musst du ihn wiefolgt anwenden: `cases prod_null_faktor_null x x h with hx hx,`
Verwende dazu `pow_two` und das Quadrat in eine Multiplikation umzuwandeln.

Für $x \\in F$ gilt: falls $x^2 = 0$ dann ist $x=0$.
"

Statement {F : Type} [Field F] (x : F) : x^2 = 0 → x = 0 := by
  intro h
  rw [pow_two x] at h
  cases (mul_eq_zero.1 h) with
  | inl hx => exact hx
  | inr hx => exact hx
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
