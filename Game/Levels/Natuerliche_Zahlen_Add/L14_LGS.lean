import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 14

Title "Lineares Gleichungssystem"

Introduction "Wir schauen uns nun ein lineares Gleichungssystem an. Gegeben ist:
```
a + b = 8
b = 3
```
Und zu zeigen ist, dass `a=5`. Auch hier könnte man direkt `linarith` anwenden
und wäre fertig. Wir wollen uns aber die Frage stellen, wie man eine Aussage
wie `h`, die ein 'und' (`∧`) enthält in zwei Aussagen einteilen kann, damit man
sie einzeln verwenden kann.

Dazu gibt es die Tactic `cases`. Für eine Aussage `h : h1 ∧ h2` teilt `cases h with f g,`
die Aussage auf, sodass man die Aussagen `f : h1` und `g : h2` erhält. Die Namen der
neuen Aussagen können wie hier (`f g`) explizit angegeben werden oder werden ansonsten
von LEAN vergeben.

Wir werden in diesem Level so vorgehen, dass wir die Aussage aufteilen um `b=3` in
`a+b=8` einzusetzten. Dafür kannst du folgenden Schritte in deinem Beweis machen:
1. Teile `h` auf. Du kannst die neuen Aussagen `hab` und `ha` nennen, um anzudeuten,
dass `hab` die Gleichung ist die sowohl `a` wie auch `b` enthält und `ha` nur `a`.
2. Setzte mithilfe von `rw` die Gleichung `hb` in `hab` ein.
3. Nutze `linarith` um mit Umformungen den Beweis zu beenden.

Seien $a, b in mathbb{N}$ mit $a+b=8$ und $b=3$. Dann ist $a=5$.
"

Statement (a b : Nat) (h : a+b=8 ∧ b=3) : a = 5 := by
  rcases h with ⟨hab, hb⟩
  rw [hb] at hab
  linarith
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
