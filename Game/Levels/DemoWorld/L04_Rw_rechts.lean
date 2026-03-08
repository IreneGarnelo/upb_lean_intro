import Game.Metadata

World "DemoWorld"
Level 4

Title "`rw` von rechts nach links"

Introduction "Wir haben im vorherigem Level gesehen, dass für die Aussage `h: a = b` der Befehl
`rw [h]`, in dem Beweisziel jedes `a` durch ein `b` ersetzt. Aber wie kann man jedes `b`
durch ein `a` ersetzen? Dazu verwendet man den Befehl `rw ← h,`. Der Pfeil steht sozusagen
dafür, dass LEAN die Aussage `h` von rechts nach links lesen soll. Du kannst den Pfeil mit
`$\\setminus$ l` (backslash + klein L) schreiben.

Es ist nun wieder die gleiche Lean Aufgabe wie im vorherigem Level gegeben. Du könntest
diese genauso lösen wie zuvor, aber erkennst du auch einen weiteren Weg der `←` verwendet?

Sei $x \\in \\mathbb{N}$ und $x=2$. Dann ist $x \\cdot 2=2 \\cdot 2$.
"

Statement (x : Nat) (h : x = 2) : x*2 = 2*2 := by
  rw [← h]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
