import Game.Metadata

World "Gruppen"
Level 6

Title "Falls $y^{-1} cdot x^{-1} cdot y cdot x = 1$, dann ist $G$ abelsch"

Introduction "Zuletzt möchten wir für Gruppen zeigen, dass falls $y^{-1} cdot x^{-1} cdot y cdot x = 1$ für
alle $x,y in G$ gilt, die Gruppe abelsch ist. Gehe dazu wiefolgt vor:
Zeige zunächst, dass die Voraussetzungen des Lemmas in level 5 erfüllt sind. Führe dazu
ein Zwischenziel ein (für diesen Teil kannst du `eq_inv_of_mul_eq_one` und `mul_inv_rev` verwenden).
Dann kannst du mit `apply inv_abelsch,` das Resultat aus level 5 anwenden. Wie kannst du nun den Beweis
schließen?

Falls $y^{-1} cdot x^{-1} cdot y cdot x$ für alle $x, y in G$, dann ist $G$ abelsch.
"

Statement {G : Type} [Group G]
(h : ∀ x y : G, y⁻¹ * x⁻¹ * y * x = 1) :
∀ x y : G, x * y = y * x := by
  Hint (hidden := true) "Brauchst du Hilfe, das Zwischenergebnis zu beweisen?
 Du kannst folgende Beweisstuktur verwenden und die sorry durch Beweisschritte austauschen:
 siehe OG code "
  have h1 : ∀ x y : G, x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by
    intros x y
    -- From the hypothesis, specialize h to x and y
    specialize h x y
    -- Regroup the terms in the hypothesis using associativity
    rw [mul_assoc] at h -- y⁻¹ * x⁻¹ * (y * x) = 1
    -- Use the hypothesis to deduce that y⁻¹ * x⁻¹ is the inverse of y * x
    have h2 : y⁻¹ * x⁻¹ = (y * x)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left h
      -- The inverse of y * x is also x⁻¹ * y⁻¹ by group properties
    have h3 : (y * x)⁻¹ = x⁻¹ * y⁻¹ := by
      exact mul_inv_rev y x
      -- Combine the two equalities: y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹
    rw [h3] at h2
    exact h2.symm
  apply inv_comm_group_comm
  exact h1
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
