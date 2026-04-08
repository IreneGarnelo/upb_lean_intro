import Game.Metadata

World "Gruppen"
Level 1

Title "Eindeutigkeit des neutralen Elements"

Introduction "Wir werden uns nun mit Gruppen auseinandersetzen. Um in einem Satz
$G$ als Gruppe zu definieren schreibt man zu Beginn der Voraussetzungen
`{G : Type} [group G]`.

Wir werden zeigen, dass das neutrale Element einer Gruppe eindeutig ist.
Schau dir zunächste die Lean-Formulierung dieses Satzes an. Wieso ist sie
gleichbedeutend damit, dass das neutrale Element eindeutig ist?

Man kann nun die Annahme, dass Element `e1` neutral ist auf Element `e2`
anwenden und umgekehrt. Verwende dazu `have h1_e2 := h1 e2` und
`have h2_e1 := h2 e1`. In diesem Fall handelt es sich um triviale Aussagen,
die mit `have` eingeführt werden, mann muss sie also nicht beweisen.
Kannst du die beiden Aussagen verwenden um das
Beweisziel zu lösen? Im Level 'Zwei Voraussetzungen - Teil 2' aus 'Erste Schritte' kannst du nachschlagen,
wie du mit und-Aussagen umgehen kannst.

Das neutrale Element einer Gruppe ist eindeutig.
"

Statement {G : Type} [Group G] (e1 e2 : G)
(h1 : ∀ a : G, e1 * a = a ∧ a * e1 = a)
(h2 : ∀ a : G, e2 * a = a ∧ a * e2 = a) :
e1 = e2 := by
  have h1_e2 := h1 e2
  have h2_e1 := h2 e1
  rw [← h1_e2.left]
  rw [h2_e1.right]
Conclusion "Beweis geschafft!"

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
