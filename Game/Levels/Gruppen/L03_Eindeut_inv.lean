import Game.Metadata

World "Gruppen"
Level 3

Title "Das inverse Element ist eindeutig"

Introduction "Nun werden wir auch die Eindeutigkeit des Inversen Elements zeigen.
Vergleiche die Formulierung des Satzes zum vorherigem, welche
Gemeinsamkeiten siehts du?

Du kannst wiefolgt umgehen: Schreibe mithilfe von `mul_one` und `one_mul`
(die Bedeutung davon kannst du unter Theorem Statements finden) das Beweisziel um,
sodass du `b*1=1*c` hast. Ersetze nun die beiden Einer durch das Produkt
von a mit jeweils den nach Voraussetzung gegebenen Inversen b und c. Wähle
dabei jeweils wie du jede Eins ersetzt so, dass du zum Schluss das Beweisziel durch
anwenden von Assoziativität (`mul_assoc`) lösen kannst.

Das Inverse eines Elements ist Eindeutig.
"

Statement {G : Type} [Group G] (a b c : G)
(hb : b * a = 1 ∧ a * b = 1) (hc : c * a = 1 ∧ a * c = 1) :
b = c := by
  rw [← mul_one b]
  rw [← one_mul c]
  conv =>
    lhs
    rw [← hc.right]
  rw [← hb.1]
  rw [mul_assoc]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
