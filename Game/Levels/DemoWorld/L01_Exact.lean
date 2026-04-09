import Game.Metadata

World "DemoWorld"
Level 1

Title "Dear Aufbau von Lean-Sätzen"

Introduction "# Struktur in Lean
Die Struktur von Sätzen mit Beweis in der Lean-Lernumgebung ist wiefolgt:
```
Statement (Voraussetzung 1)
          (Voraussetzung 2) :
          Folgerung := by
Beweis
```

# Beweisschritte
In Lean löst man Beweise, indem man Taktiken verwendet, die Beweisschritte
abbilden. Nach jedem Beweischritt muss man mit Enter eine neue Zeile starten, um dem Program mitzuteilen,
dass er den Schritt verarbeiten kann. In diesem Level werden wir die `exact` Taktik kennenlernen.
Diese kann verwendet werden, wenn eine der Aussagen `h`, die man in dem Beweiszustand sieht mit dem
Beweisziel übereinstimmt. Dann schreibt man `exact h`. Das bedeutet in etwa so viel wie: 'Die zu
Beweisende Aussage ist exakt die Aussage h.'
Es gibt viele Taktiken in Lean, du kannst den Teil davon, den du für diese Lernumgebung
brauchst in der rechten Spalte unter 'Tactics' finden, wir werden diese aber Schritt für
Schritt einführen.

# Erste Aufgabe
Wir möchten nun diese Taktik verwenden, um folgenden Satz zu beweisen:
Sei $x$ eine natürliche Zahl und $x=2$. Dann ist $x=2$.
Lies als erstes die Formulierung in Lean und versuche den Satz dort wiederzuerkennen.
Nutze dann die `exact` Taktik um den Beweis zu lösen."

Statement (x : Nat) (h : x = 2) : x = 2 := by
  Hint "Der Beweisschritt lautet `exact h`"
  exact h
Conclusion "Beweis geschafft!"

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
