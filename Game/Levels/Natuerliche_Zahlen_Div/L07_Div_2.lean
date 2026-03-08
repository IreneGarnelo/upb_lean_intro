import Game.Metadata

World "Natuerliche_Zahlen_Div"
Level 7

Title "Existenz Divisor und Rest"

Introduction "Bevor wir uns unserem finalem Level widmen, indem wir die Aussage der
Division mit Rest für $r < m$ zeigen, brauchen wir noch ein Lemma, das wir
hier auslagern, damit der Beweis im nächsten Level nicht so kompliziert
wird.

Das Lemma wird dazu nutzen, im Induktionsschritt des Beweises der Division
mir Rest zu zeigen, dass $r < m$. Aus der Induktionsvoraussetzung haben wir:
```
hr : r < m
hq : d = m*q+r
```
Außerdem wird dieses Lemma in einer Fallunterscheidung verwendet, in dem Fall
das `d.succ` kein Vielfaches von `m` ist, also:
```
hq' : ¬ ∃ (q':ℕ), d.succ=m*q'
```

In diesem Level musst du den Beweis nicht selber machen aber solltest ihn lesen
und nachvollziehen. Dazu kannst du den Beweis direkt in das Feld kopieren:
```
  /- zuerst zeigen wir, dass r+1 ≤ m (da r < m) -/
  have hr_succ_le_m : r + 1 ≤ m,
  { exact succ_le_of_lt hr, },
  /- nun führen wir einen Widerspruchbeweis. Wenn wir nämlich annehmen,
  dass r+1 ≥ m, dann können wir danach mir hr_succ_le_m Gleichheit folgern -/
  by_contra h_contr,
  push_neg at h_contr,
  /- nun folgern wir r+1=m -/
  have hr1_m : r+1=m,
  {exact le_antisymm hr_succ_le_m h_contr,},
  /- damit können wir zeigen, dass d+1=m*(q+1) ist -/
  have d_mult_q : d.succ = m*(q+1),
  {rw [succ_eq_add_one],
  linarith,
  },
  /- Um nun einen Widerspruch herzustellen müssen wir dies noch
  als Existenzaussage formulieren. -/
  have h_eq : ∃ (q : ℕ), d.succ = m * q := ⟨q+1, d_mult_q⟩,
  /- Wir haben nun zwei widersprüchliche Aussagen im Beweiszustand.
  Mit contradiction kann der Widerspruchsbeweis beender werden. -/
  contradiction,
```
Die Kommentare führen dich durch den Beweis. Es werden zwei Sätze verwendet,
die du nicht kennst. Hier ist ihre Bedeutung:
```succ_le_of_lt {a b : ℕ} (h : a < b) : succ a ≤ b
le_antisymm : ∀ {a b : ℕ}, (a ≤ b ∧ b ≤ a) → a = b```

Seien $m,d,q,r ∈ \mathbb{N}$ mit $r < m$ und $d=m⬝q+r$. Falls es kein $q' ∈ \mathbb{N}$ gibt
sodass $d+1=m⬝q$, dann gilt, dass $r+1 < m$
"

Statement (m d q r : ℕ) (hr : r < m) (hq : d = m*q+r) (hq' : ¬ ∃ (q':ℕ), d.succ=m*q') : r+1<m := by
  /- zuerst zeigen wir, dass r+1 ≤ m (da r < m) -/
  have hr_succ_le_m : r + 1 ≤ m,
  { exact succ_le_of_lt hr, },
  /- nun führen wir einen Widerspruchbeweis. Wenn wir nämlich annehmen,
  dass r+1 ≥ m, dann können wir danach mir hr_succ_le_m Gleichheit folgern -/
  by_contra h_contr,
  push_neg at h_contr,
  /- nun folgern wir r+1=m -/
  have hr1_m : r+1=m,
  {exact le_antisymm hr_succ_le_m h_contr,},
  /- damit können wir zeigen, dass d+1=m*(q+1) ist -/
  have d_mult_q : d.succ = m*(q+1),
  {rw [succ_eq_add_one],
  linarith,
  },
  /- Um nun einen Widerspruch herzustellen müssen wir dies noch
  als Existenzaussage formulieren. -/
  have h_eq : ∃ (q : ℕ), d.succ = m * q := ⟨q+1, d_mult_q⟩,
  /- Wir haben nun zwei widersprüchliche Aussagen im Beweiszustand.
  Mit contradiction kann der Widerspruchsbeweis beender werden. -/
  contradiction,
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
