import Game.Levels.DemoWorld
--import Game.Levels.Vergleiche
import Game.Levels.Gruppen
import Game.Levels.Koerper
import Game.Levels.Natuerliche_Zahlen_Add
import Game.Levels.Natuerliche_Zahlen_Mult
import Game.Levels.Natuerliche_Zahlen_Div

-- Here's what we'll put on the title screen
Title "Die Lean-Beweiswerkstatt"
Introduction
"
Willkommen zu der interaktiven Lernumgebung zur Einführung in den Theorembeweiser Lean.
In dieser Lernumgebung wird anhand mathematisch simpler Aufgaben Lean Schritt für
Schritt gelernt.

Für diese Lernumgebung sind keine Vorkenntnisse zu Theorembeweisern notwendig.

Es gibt verschiedene Bereiche aus denen du auf der Startseite auswählen kannst.
Jeder Bereich hat dann mehrere Level. Am besten fängst du mit dem Bereich Erste
Schritte an.
"

Info "
Diese Lernumgebung wurde von Irene Garnelo entwickelt. Dazu wurde die von dem ADAM
Projekt bereitgestellte Plattform: [Lean Game Server](https://adam.math.hhu.de/#/)
verwendet.
"
Dependency DemoWorld → Gruppen
Dependency Gruppen → Koerper
Dependency DemoWorld → Natuerliche_Zahlen_Add
Dependency Natuerliche_Zahlen_Add → Natuerliche_Zahlen_Mult
Dependency Natuerliche_Zahlen_Mult → Natuerliche_Zahlen_Div

/-! Information to be displayed on the servers landing page. -/
Languages "de"
CaptionShort "Einführung in Lean"
CaptionLong "Eine Einführung auf Deutsch in den Theorembeweiser Lean4 für Mathematikstudierende"
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
