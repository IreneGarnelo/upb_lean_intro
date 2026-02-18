import Game.Metadata

World "DemoWorld"
Level 2

Title "Aussagen anwenden: Die `rw`-Taktik"

Introduction "Wir werden nun eine weitere Taktik namens `rw` (Abkürzung für rewrite) kennenlernen.
Mit dieser Taktik kann man Aussagen auf das Beweisziel anwenden.

Wenn h eine Aussage ist (z.B. `h : a = b`), dann bewirkt `rw h,`, dass LEAN die Aussage
`h` in das Beweisziel einsetzt. In diesem Fall würde Lean in dem Beweisziel jedes `a` mit
einem `b` ersetzten. Man kann angeben, an welcher Stelle des Beweiszieles die Aussage
angewandt werden soll, indem man `rw h x,` schreibt. Wenn nur eine Stelle möglich ist,
dann kann man das Argument weglassen.

Wir werden folgende Aussage zeigen: <br>
Sei $x$ eine natürliche Zahl und $x=2$. Dann ist $x \\cdot 2=2 \\cdot 2$. <br>
Dazu muss man die gegebene Aussage $x=2$ einfach in das Beweisziel einsetzen. Probiere
das mit dem `rw` Befehl aus und vergesse nicht das Komma am Ende der Zeile."

Statement (x : Nat) (h : x = 2) : x*2 = x*x := by
  Hint "Der Beweisschritt lautet `rw [h]`"
  rw [h]

Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic rw
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
