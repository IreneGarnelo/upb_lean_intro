import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 3

Title "Addition natürlicher Zahlen"

Introduction "Man kann die Addition zweier natürlichen Zahlen rekursiv anhand der Peano-Axiome
definieren.
- Für $a in mathbb{N}$ sei $a+0=a$
- Für $a,d in mathbb{N}$ sei $a+$`succ`$(d) = $`succ`$(a+d)$

Nach dem Prinzip der Induktion ist dann die Addition für alle Paare von natürlichen
Zahlen definiert.

Die beiden Aussagen, die die Addition definieren, sind in LEAN implementiert und
haben jeweils den Namen `add_zero` und `add_succ`. Auch diese Aussagen können mit
dem Befehl `rw` verwendet werden. `rw add_zero,` wandelt die Aussage `b+zero` in `b`
um.

In diesem Level werden wir eine Aussage beweisen, in der die Addition der
natürlichen Zahlen vorkommt. Die Aussage ist: Sei $a in mathbb{N}$.
Dann ist `succ`$(a)+0=$`succ`$(a+0)$. Wir können diese Aussage beweisen,
indem wir die Aussage `add_zero` mit `rw` auf das Beweisziel anwenden.

In dieser Aussage kommen zwei Ausdrücke der Form $n+0$ vor. Man kann bei der
Tactic rw konkretisieren, auf welche der beiden Stellen rw angewandt werden
soll. Probiere in dem Beweis erst `rw [add_zero(a)],` aus. Lösche diese Zeile
und schreibe stattdessen `rw [add_zero(a.succ)],`. Siehst du den Unterschied im
Beweisziel?

$a+$`succ`$(0)=$`succ`$(a)$
"

Statement (a : Nat) : succ a + zero  = succ (a + zero) := by
  rw [Nat.add_zero a]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
