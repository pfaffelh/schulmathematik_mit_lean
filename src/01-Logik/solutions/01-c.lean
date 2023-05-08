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
  split,
  exact hnP,
  intro h,
  exfalso,
  exact h,  
end

-- Aufgabe 2) Etwas komplizierter...
example (hnP : ¬P) (hQ : Q) : ( P ↔ ¬Q ) :=
begin
  split,
  intros hP hQ, 
  apply hnP,
  exact hP,
  intro hnQ, 
  exfalso, 
  apply hnQ,
  apply hQ,
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
  intro hP,
  triv, 
end

-- Aufgabe 4a) Eine Aussage ist genau dann nicht wahr, wenn sie falsch ist. 
example : ¬true ↔ false :=
begin
  split,
  {
    intro h1, 
    apply h1, 
    triv,
  },
  {
    intros h1 h2,
    exact h1,
  }  
end

-- Aufgabe 4b) Eine Aussage ist genau dann nicht falsch, wenn sie wahr ist. 
example : true ↔ ¬ false :=
begin
  split,
  {
    intros h1 h2, 
    exact h2,   
  },
  {
    intros h1, 
    triv, 
  },
end


-- Aufgabe 5) Ob die Aussage P wahr ist, oder aus einer wahren Aussage folgt, ist egal:
example : (true → P) ↔ P :=
begin
  split, 
  {
    intro h1, 
    apply h1, 
    triv,
  },
  { 
    intros h1 h2,
    exact h1,
  }
end

-- Aufgabe 6) Hier eine kleine Wiederholung mit einer doppelten Negation.
example : P → ¬¬P := 
begin
  intros hP hnP,
  apply hnP hP,
end

/- 
  Wir kommen nun zum Widerspruchsbeweis. Ist das Ziel P und wollen dies durch Widerspruch beweisen, so fügen wir eine Annahme ¬P hinzu, und müssen das auf einen Widerspruch bringen. Das bedeutet, wir müssen false zeigen.
-/

-- Wir zeigen die Rückrichtung von Aufgabe 6.
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
  split,  
  {
    intros hPQ hnQ hP,
    apply hnQ,
    apply hPQ,
    apply hP,
  },
  {  
    intros h1 hP,
    by_contra h, 
    apply h1, 
    exact h, 
    exact hP,
  },
end

