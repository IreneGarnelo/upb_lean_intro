import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 10

Title "Kommutativität der rechten Summanden"

Introduction "Das Ziel dieses Levels ist für natürliche Zahlen $a,b,c$ zu zeigen, dass $a+b+c=a+c+b$ gilt.
Das sieht vielleicht erstmal danach aus, dass du nur `add_comm,` anwenden muss.
Aber LEAN ist links-assoziativ. Das bedeutet, dass diese Aussage mit Klammern so
geschrieben werden kann: $(a+b)+c=(a+c)+b$. Um dieses Lemma zu zeigen, wirst du also
auch die Assoziativität verwenden. Dieses Lemma wird dir in zukünftigen Beweisen etwas
Schreibarbeit sparen.

In diesem Level werden dir die Beweischritte 'in normaler Sprache' vorgegeben, die du
dann in LEAN-Spache umsetzten kannst. Der Beweis besteht aus drei Schritten. Wir empfehlen
bei jedem Schritt zu spezifizieren, auf welchen Teil sich rw beziehen soll.

1. Wende die Assoziativität der Addition an, um in der linken Seite des Ausdrucks
umzuklammern. Das Beweisziel a + b + c = a + c + b soll zu a + (b + c) = a + c + b werden.
2. Wende die Kommutativität der Addition an, um das b und c in der linken Seite des
Ausdrucks umzuklammern. Das Beweisziel a + (b + c) = a + c + b soll zu
a + (c + b) = a + c + b werden.
3. Wende die Assozitivität der Addition nun rückwerts an, um in der linken Seite des
Ausdrucks umzuklammern. Das Beweisziel a + (c + b) = a + c + b soll zu
a + c + b = a + c + b werden und somit den Beweis lösen.

Seien $a, b, c \\in \\mathbb{N}$. Dann ist $a+b+c=a+c+b$.
"

Statement (a b c: Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc a b c]
  rw [Nat.add_comm b c]
  rw [← Nat.add_assoc a c b]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
