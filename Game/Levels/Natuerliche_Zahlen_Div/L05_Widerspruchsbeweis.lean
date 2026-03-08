import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 5

Title "Der Widerspruchsbeweis"

Introduction "In LEAN wird für einen Widerspruchsbeweis die Tactic `by_contra` verwendet.
Angenommen, du möchtest die Aussage P mit einem Widerspruchsbeweis beweisen.
Dann verwendest du als erstes `by_contra` um den Widerspruchsbeweis zu starten.
Du wirst sehen, dass nun `¬P` unter den gegebenen Aussagen ist, und das neue
Beweisziel `⊢ false` ist. Das bedeutet, dass das Ziel ist, einen Widespruch zu
erzeugen.

Ein Widerspruchsbeweis sieht also zum Beispiel so aus:

```
theorem no_n_succ_eq_zero : ¬∃ (n : ℕ), n+1=0 :=
begin
by_contra hex,
obtain ⟨n, hn⟩ := hex,
linarith,
end
```
Dabei kann man nach `by_contra` einen Namen (hier `hex`) für die Widerspruchsannahme geben.

In diesem Level werden wir mit einem Widerspruchsbeweis zeigen, dass es keine natürliche
Zahl $a<4$ gibt, die ein echtes Vielfaches von $4$ ist.

Um den LEAN-Beweis zu schreiben, kannst du diese Schritte verwenden:
1. Widerspruchsannahme: Angenommen es gibt $a, b in mathbb{N}$ mit $b>0$, $a<4$ und $a=b⬝4$.
2. Seien nun $a, b in mathbb{N}$ sodass $b>0$, $a<4$ und $a=b⬝4$.
3. Wir geben der Aussage $b>0$ den Namen hb, der Aussage $a<4$ den Namen ha und der Aussage
$a=b⬝4$ den Namen hab.
4. Wir zeigen nun zuerst, dass $ageq4$, indem wir die Aussage hnm und arithmetische
Operationen verwenden.
5. Mit dieser neuen Aussage und arithmentischen Operationen lässt sich ein Widerspruch
zur Aussage hn herleiten.

Es gibt kein $a, b \\in \\mathbb{N}$ mit $b>0$, $a<4$ und $a=b⬝4$.
"

Statement : ¬ ∃ (a b : Nat), b ≥ 1 ∧ a < 4 ∧ a = b * 4 := by
  by_contra h_contr
  rcases h_contr with ⟨n, m, hmpos, hnlt, hnm⟩
  have a_bigger_four : n ≥ 4 := by
    have hmul : m * 4 ≥ 1 * 4 := by
      exact Nat.mul_le_mul_right 4 hmpos
    rw [hnm]
    exact hmul
  exact Nat.not_lt.mpr a_bigger_four hnlt
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
