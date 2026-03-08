import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 8

Title "Existenz Divisor und Rest"

Introduction "Nun können wir den Satz zum Beweis mit Rest zeigen. Dazu fehlt dir nur noch eine
Tactic, um das Lemma aus dem vorherigem Level anwenden zu können. Wenn die Voraussetzungen
eines anderen Satz in dem Beweiszustand gegeben sind und das Beweisziel das Ergebnis
dieses Satzes ist, kann mit `apply Satz Voraussetzungen,` das Ziel gelöst werden.

Wenn man zum Beispiel der Satz:
```
theorem mul_gerade (a b : ℕ) (hger : ∃ c : ℕ, a=2*c) : ∃ d : ℕ, a*b = 2*d
```
bereits bewiesen wurde und der Beweiszustand:
```
c d : ℕ
hc: ∃ (e : ℕ), c = 2 * e
⊢ ∃ (f : ℕ), c * d = 2 * f
```
ist kann man `apply mul_gerade c d hc,` angewandt werden um den Beweis
zu lösen. Wichtig ist die Reihenfolge der Voraussetzungen, diese dürfen
aber natürlich im neuen Kontext einen anderen Namen haben.

In diesem Level kannst du dich an der Struktur des vereinfachten Beweises orientieren:
```
theorem exist_divisor_rest_gr (n m : ℕ) (hm : m > 0) : ∃ q r : ℕ, n = m * q + r :=
begin
  induction n with d hd,
  { use [0, 0],
    simp [hm], },
  { by_cases hq' : ∃ q', d.succ = m*q',
    { obtain ⟨q', hq'⟩ := hq',
      use [q', 0],
      simp [hq'],},
    { use [0, d.succ],
      simp, } }
end

mit dem Unterschied, dass du nach dem `use` Befehl nun eine Aussage mit `∧` zeigen
musst und hier also `split` verwenden solltest.
```

Seien $n,m ∈ \mathbb{N}$ mit $m>0$. Dann gilt: Es gibt $q,r\in \mathbb{N}$ mit $n = m⬝q + r$ und $r < m$.
"

Statement (m n : ℕ) (hm : m > 0) : ∃ q r : ℕ, n = m * q + r ∧ r < m := by
  induction n with d hd,
  { -- Induktionsanfang
    use [0, 0]
    split
    { -- Zeige: 0=m*0+0
      simp, }
    { -- Zeige: 0 kleiner m
      exact hm, } }
  { -- Induktionsschritt
    by_cases hq2 : ∃ q', d.succ = m*q'
    { -- Fall m teilt d+1
      obtain ⟨q, hq⟩ := hq2
      use [q, 0]
      split
      { -- Zeige: d+1=m*q+0
        simp [hq]
        }
      { -- Zeige: r kleiner m
        exact hm } }
    { -- Fall m teilt d+1 nicht
      obtain ⟨q, r, ⟨hq, hr⟩⟩ := hd
      use [q, r + 1]
      split
      { -- Zeige: d+1 = m * q + (r + 1)
        rw [hq]
        rw [add_succ] }
      { -- Zeige r kleiner m
        apply lemma_div m d q r hr hq hq2
        }
    }
  }
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
