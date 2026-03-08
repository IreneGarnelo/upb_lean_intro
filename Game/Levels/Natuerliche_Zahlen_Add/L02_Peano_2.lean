import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 2

Title "Die Peano Axiome - Teil 2"

Introduction "In diesem Level werden wir das in Level 1 Gelernten üben und ein weiteres Feature des `rw` Befehls verstehen.

Vielleicht hast du gemerkt, dass es eine linke Spalte gibt. Hier kannst du alle
Tools finden, die du zum Beweisen brauchst. Das sind einerseits die Befehle (wie
z.B. `rw`), die in LEAN Tactics heißen. Andererseits sind das die Axiome und Aussagen,
die wir bereits eingeführt/bewiesen haben. Diese sind in der Kategorie Theorem
statements. Umso weiter du bist, umso mehr Inhalt wirst du hier finden.

Wir haben im vorherigem Level gesehen, dass für die Aussage `h: a = b` der Befehl
`rw [h],` in der zu zeigenden Aussage jedes `a` durch ein `b` ersetzt. Aber wie
kann man jedes `b` durch ein `a` ersetzen? Dazu verwendet man den Befehl
`rw [← h],`. Der Pfeil steht sozusagen dafür, dass LEAN die Aussage h von rechts
nach links lesen soll. Du kannst den Pfeil mit  l (backslash + klein L)
schreiben.

Du kannst das untenstehende Lemma ähnlich wie Level 1 lösen, aber erkennst du
auch einen weiteren Weg der `←` verwendet?

Falls `succ`$(a) = b$ und `succ`$(b)= c$, dann `succ`$($`succ`$(a)) = c$
"

Statement (a b c : Nat) (h : succ a = b) (g : succ b = c): succ (succ a) = c := by
  rw [← g]
  rw [h]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
