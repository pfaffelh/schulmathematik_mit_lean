import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/- 
  "Aus falschem folgt Beliebiges" heißt übersetzt, dass false → P immer wahr ist, egal was P ist. Hat man also das Ziel P, und würde diese Aussage mit _apply_ anwenden, würde man bei denselben Hypothesen das neue Ziel false haben. Diese Taktik heißt _exfalso_. 
-/

example (h : false) : P :=
begin
  exfalso,
  exact h,
end

-- Aufgabe 1) ¬P heißt ja, dass P falsch ist. Anders ausgedrückt, ist dann P↔false. Dies zeigen wir nun:
example (hnP : ¬P) : P ↔ false :=
begin
  sorry,  
end

-- Aufgabe 2) Etwas komplizierter...
example (hnP : ¬P) (hQ : Q) : ( P ↔ ¬Q ) :=
begin
  sorry,
end


/- 
  Eine wahre Aussage ist immer wahr, ganz egal welche Hypothesen gelten sollen. Ist das Ziel also true, so kann man es mit _triv_ erreichen.
-/

example : true :=
begin
  triv,
end

-- Aufgabe 3: Gilt eine Aussage, so folgt daraus jede wahre Aussage:
example : P → true :=
begin
  sorry, 
end

-- Aufgabe 4a) Eine Aussage ist genau dann nicht wahr, wenn sie falsch ist. 
example : ¬true ↔ false :=
begin
  sorry,
end

-- Aufgabe 4b) Eine Aussage ist genau dann nicht falsch, wenn sie wahr ist. 
example : true ↔ ¬ false :=
begin
  sorry,
end


-- Aufgabe 5) Ob die Aussage P wahr ist, oder aus einer wahren Aussage folgt, ist egal:
example : (true → P) ↔ P :=
begin
  sorry,
end

-- Aufgabe 6) Hier eine kleine Wiederholung mit einer doppelten Negation.
example : P ↔ ¬¬P := 
begin
  sorry,
end

/- 
  Wir kommen nun zum Widerspruchsbeweis. Ist das Ziel P und wollen dies durch Widerspruch beweisen, so fügen wir eine Annahme ¬P hinzu, und müssen das auf einen Widerspruch bringen. Das bedeutet, wir müssen false zeigen.
-/

-- Wir zeigen die Rückrichtung von Aufgabe 5.
example : ¬¬P → P := 
begin
  intro h1, 
  by_contra h2,
  apply h1,
  exact h2, 
end

-- Aufgabe 7: Bei der Rückrichtung führt ein apply auf zwei neue Ziele!
example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  sorry,
end

