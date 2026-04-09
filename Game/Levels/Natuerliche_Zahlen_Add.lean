import Game.Levels.Natuerliche_Zahlen_Add.L01_Peano
import Game.Levels.Natuerliche_Zahlen_Add.L02_Peano_2
import Game.Levels.Natuerliche_Zahlen_Add.L03_Addition
import Game.Levels.Natuerliche_Zahlen_Add.L04_succ_zero
import Game.Levels.Natuerliche_Zahlen_Add.L05_Eins
import Game.Levels.Natuerliche_Zahlen_Add.L06_Addition_0_links
import Game.Levels.Natuerliche_Zahlen_Add.L07_Assoziativ
import Game.Levels.Natuerliche_Zahlen_Add.L08_add_succ_left
import Game.Levels.Natuerliche_Zahlen_Add.L09_Add_komm
import Game.Levels.Natuerliche_Zahlen_Add.L10_add_right_komm
import Game.Levels.Natuerliche_Zahlen_Add.L11_Existenzbeweis
import Game.Levels.Natuerliche_Zahlen_Add.L12_Lineare_gleichung
import Game.Levels.Natuerliche_Zahlen_Add.L13_Lineare_gleichung_2
import Game.Levels.Natuerliche_Zahlen_Add.L14_LGS
import Game.Levels.Natuerliche_Zahlen_Add.L15_LGS_2

World "Natuerliche_Zahlen_Add"
Title "Natürliche Zahlen: Addition"

Introduction "
Die natürlichen Zahlen können mit Peanos Axiomen eindeutig definiert werden. Die
Axiome lauten wie folgt:
- $A_1$: $0$ (in LEAN: `zero`) ist eine natürliche Zahl
- $A_2$: Es gibt eine injektive Abbildung `succ`$: N \\to N$, die für jede natürliche Zahl ihren Nachfolger angibt.
- $A_3$: $0$ ist nicht der Nachfolger einer natürlichen Zahl.
- $A_4$: Das Prinzip der Induktion: Enthält eine Menge die $0$ und für jede enthaltene natürliche Zahl $n$ auch ihren Nachfolger `succ`$(n)$, so enthält sie alle natürlichen Zahlen.

In LEAN kann man die Anwendung der Abbildung `succ` auf `a` sowohl als `succ a` als auch
als `a.succ` schreiben.

Wir werden mit der Klasse Nat arbeiten, die genau nach den Axiomen von Peano definiert ist.
"
