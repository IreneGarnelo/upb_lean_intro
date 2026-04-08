import Game.Metadata

World "Gruppen"
Level 4
TheoremTab "Gruppen"

Title "Falls jedes Element Selbstinvers ist, ist G abelsch"

Introduction "In deisem Level werden wir zeigen, dass wenn jedes Element einer Gruppe $G$ selbstinvers ist,
$G$ abelsch ist.

Beginne mit `intros a b,` um das Beweisziel von der allgemeinen Abelheit der Gruppe auf die
Aussage $a b = b a$ für konkrete $a,b$ überzuführen.

Das die Verknüpfung zweier Elemente $a b$ auch wieder ein Element der Gruppe ist,
gilt auch für dieses, dass es selbstinvers ist. Führe die Aussage `h1 : (a * b)⁻¹ = a * b`
ein und Beweise sie. (Falls du nachschlagen möchtest, wie du mit Zwischenzielen
umgehst, schlage die Taktik `have` nach).

Zusätzlich gilt aber für das Inverse einer Verknüpfung auch die allgemeine Eigenschaft:
$(a b)^{-1}=b^{-1} a^{-1}$. Führe auch dies als Aussage `h2` ein. Diese Aussage
ist in Lean implementiert als `mul_inv_rev`, du kannst diesen Satz also zusammen mit `rw`
anwenden.

Nun kannst du h1 in h2 einsetzen. Ersetze zulezt in `h2`: `a⁻¹` durch `a` und `b⁻¹` durch `b`,
indem du `h` anwendest.

Falls $g \\cdot g = 1$ für alle $g \\in G$, dann ist $G$ abelsch.
"

Statement {G : Type} [Group G]
(h : ∀ a : G, a⁻¹ = a) :
∀ a b : G, a * b = b * a := by
  intros a b
  have h1 : (a * b)⁻¹ = a * b := by
    rw [h]
  have h2 : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
    rw [mul_inv_rev a b]
  rw [h1] at h2
  rw [h a] at h2
  rw [h b] at h2
  exact h2
Conclusion "Beweis geschafft!"


NewTheorem mul_inv_rev
-- NewDefinition Nat Add Eq
