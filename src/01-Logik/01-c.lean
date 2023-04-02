import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/- 
  "Aus falschem folgt Beliebiges" heißt übersetzt, dass false → P immer wahr ist, egal was P ist. Hat man also das Ziel P, und würde diese Aussage mit apply anwenden, würde man bei denselben Hypothesen das neue Ziel false haben. Diese Taktik heißt exfalso. 
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
  Eine wahre Aussage ist immer wahr, ganz egal welche Hypothesen gelten sollen. Ist das Ziel also true, so kann man es mit triv schließen.
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
  intro h1, 
  apply h1, 
  triv,
  intros h1 h2,
  exact h1,
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
  intro h1, 
  apply h1, 
  triv,
  intros h1 h2,
  exact h1,
end

-- Aufgabe 6) Hier eine kleine Wiederholung mit einer doppelten Negation.
example : P → ¬¬P := 
begin
  intros hP hnP,
  apply hnP, 
  exact hP,
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
  split,  
  intros hPQ hnQ hP,
  apply hnQ,
  apply hPQ,
  apply hP,
  intros h1 hP,
  by_contra h, 
  apply h1, 
  exact h, 
  exact hP,
end




/-
  Nun kommen wir zu binären Verknüpfungen von Aussagen, also P ∧ Q bzw P ∨ Q. Diese können entweder als Hypothese auftreten, oder als Ziel. Entsprechend gibt es vier verschiedene Fälle, wie wir mit solchen Fällen umgehen können.
-/




-- 1c) split, cases, left, right

-- split, exact, intro
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end

example : (P ∧ Q) → (P ∨ Q) := 
begin
intro h, left, 
cases h with hP hQ, 
--  rintro ⟨ hP, hQ ⟩, 
exact hP,
end

example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  split,
  intro h, 
  cases h with hP hQ, 
  left, exact hP, 
  by_cases P, 
  left, exact h, 
  right, 
  intro nQ, 
  exfalso, apply nQ, exact hQ, 
  sorry, 
end



-- 1d) add exfalso, triv, negation, by_cases
-- intro, exfalso, exact

example : (P ∨ ¬P) → true :=
begin
  rintro (hP | hnP);
  triv,  
end

 -- intro, cases
example : (P ∧ ¬P) → false :=
begin
  intro h, cases h with hP hnP, 
--  rintro ⟨hP, hnP⟩, 
  apply hnP,
  exact hP, 
end








-- 2) Einführung neuer Hypothesen mit by_cases und have

-- 1g) add by_cases
example : (P ∨ ¬P ) :=
begin
  by_cases P with hP hnP,
  left, exact h,
  right, exact h,
end

example : P → P := 
begin
  have h : P ↔ P, refl, apply h.1,
end



-- 3) Abkürzzungen


-- 1f) refl, rw
example : P ↔ P := 
begin
  refl,
end

example : P = P :=
begin
  refl, 
end

-- 3a) rintro(s), rcases, obtain



example : (P → Q) ∧ (Q → R) → (P → R) := 
begin
  rintro ⟨ hPQ, hQR ⟩ hP,
  exact hQR (hPQ hP), 
end

-- intro, cases, exact
-- rintro 

example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q :=
begin
  by_cases P,
  exact hPQ h, 
  exact hnPQ h,  
end

-- obtain

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  obtain hQ := hPQ hP,
  obtain hnQ := hPnQ hP,
  apply hnQ, 
  exact hQ,
end

example : (P ∨ Q) → (¬Q → P) := 
begin
  rintros (hP | hQ) h, 
  exact hP,
  exfalso, 
  apply h, 
  exact hQ, 
end



























--change a bit
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( (Q ↔ R) ∧ (R ↔ T)) :=
begin
  split, 
  { 
    split,
    exact hQR,
    intro hR, 
    exact hPQ (hTP (hRT hR)),
  },
  split, 
  exact hRT,
  intro hT,
  exact hQR (hPQ (hTP hT)),
end
