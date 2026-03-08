import Game.Metadata
open Nat

World "Natuerliche_Zahlen_Add"
Level 1

Title "Die Peano Axiome"

Introduction "Die natürlichen Zahlen können mit Peanos Axiomen eindeutig definiert werden. Die
Axiome lauten wie folgt:
- $A_1$: $0$ (in LEAN: `zero`) ist eine natürliche Zahl
- $A_2$: Es gibt eine injektive Abbildung `succ`$: mathbb{N} to mathbb{N}$, die für jede natürliche Zahl ihren Nachfolger angibt.
- $A_3$: $0$ ist nicht der Nachfolger einer natürlichen Zahl.
- $A_4$: Das Prinzip der Induktion: Enthält eine Menge die $0$ und für jede enthaltene natürliche Zahl $n$ auch ihren Nachfolger `succ`$(n)$, so enthält sie alle natürlichen Zahlen.

In LEAN kann man die Anwendung der Abbildung `succ` auf `a` sowohl als `succ(a)` als auch
als `a.succ` schreiben.

Aus diesen Axiomen werden wir alles herleiten und beweisen, was wir in dieser Einheit
vorhaben. In diesem level werden wir folgende Aussage zur Funktion `succ` zeigen: Für die natürlichen Zahlen a und b gilt: falls `succ(a)=b` dann `succ(succ(a))=succ(b)`.

Diese Aussage kann man direkt zeigen, indem man die gegebene Hypothese `succ(a)=b` in die
zu zeigende Aussage `succ(succ(a))=succ(b)` einsetzt und somit `succ(b)=succ(b)` erhält.

Wir schauen uns nun an, wie das in LEAN funktioniert. Wir werden mit der Klasse
N arbeiten, die genau nach den Axiomen von Peano definiert ist.

Als Erstes muss man das Lemma definieren, das man beweisen möchte. Dies besteht aus drei
Teilen.
- Name: Der Name kann beliebig gewählt werden, ist im besten Fall aber eine gute
Beschreibung des Lemmas. Hier kann man zum Beispiel “succ_succ” wählen, um anzudeuten,
dass es um die Zweifachanwendung der Abbildung `succ` geht.
- Voraussetzungen: Diese stehen zwischen dem Namen und dem Doppelpunkt. In diesem Fall
sind das, dass a und b natürliche Zahlen sind und die Aussage h, dass `succ(a)=b`.
- Folgerung: Diese steht zwischen dem Doppelpunkt und dem Definitionszeichen. In diesem
Fall also, `succ(succ(a))=b`.

Der Beweis folgt zwischen dem `begin` und dem `end`. Zu Beginn der Bearbeitung steht im
Beweis immer `sorry`. Dies ist ein Keyword, was so viel bedeutet wie: 'Hier fehlt ein
Teil des Beweises'. Du kannst dieses Keyword verwenden, wenn ein Beweis überprüft werden
soll, bei dem dir noch ein Teil fehlt. LEAN wird bestätigen, dass der Beweis stimmt, aber
mit dem warning 'uses `sorry`' darauf hinweisen, dass noch etwas zu tun ist. Lösche als
Erstes das `sorry`, um mit dem Beweis zu starten.

Wir haben oben bereits beschrieben, wie der Beweis mathematisch funktioniert. Wie
übertragen wir die Idee in LEAN? Dazu gibt es den `rw` (rewrite) Befehl. Wenn `h` eine
Aussage ist (z.B. $a=b$), dann bewirkt `rw [h],`, dass LEAN die Aussage `h` in der zu
zeigenden Aussage einsetzt (im Beispiel würde also in der zu zeigenden Aussage jedes $a$
mit einem $b$ ersetzt werden). Probiere also den Befehl `rw [h],` aus. Das Komma am Ende
jedes LEAN-Befehls ist sehr wichtig. Wenn du Fehlermeldungen bekommst, die du nicht
verstehst, überprüfe deinen Code auf fehlende Kommata.

Die rechte Spalte:
Diese Spalte wird als Beweiszustand bezeichnet. Hier gibt LEAN dynamisches Feedback.
Bis auf die letzte Zeile stehen hier die gegebenen Aussagen, in diesem Fall zum Beispiel,
dass a und b natürliche Zahlen sind und die
Aussage `h`. In der letzten Zeile, nach dem `⊢` Symbol, steht immer das aktuelle Beweisziel,
also das, was gerade zu  zeigen ist. Wenn man am Anfang des Beweises steht, ist das
noch die ganze Aussage des Satzes. Nachdem man `rw [h],` eingibt, sieht man, dass sich
der Zustand ändert. In diesem Fall kommt die Nachricht `Proof complete!`, die uns
angibt, dass wir fertig sind. In längeren Aufgaben würde hier das neue Ziel stehen. Ein
Beweis ist dann zuende, wenn eine Aussage der Form 'a=a' als Beweiszustand entsteht.

Falls `succ`$(a) = b$, dann `succ`$($`succ`$(a)) = $`succ`$(b)$
"

Statement (a b : Nat) (h : succ a = b): succ (succ a) = succ b := by
  rw [h]
Conclusion "Beweis geschafft!"

/- Use these commands to add items to the game's inventory. TODO: do we need refl? -/

NewTactic exact
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
