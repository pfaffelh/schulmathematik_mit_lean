import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Bisher haben sich die verwendeten Hypothesen immer durch Umformung bereits vorhandener Hypothesen ergeben. Das muss aber keineswegs immer so sein, weil man ja neue Hypothesen hinzufügen kann, die man aber auch beweisen muss. Wir lernen hier _have_ und _by_cases_ kennen.
-/

















-- Hier braucht man irgendwann by_cases!

-- braucht auch by_cases
-- Aufgabe 5) 
example : (P ∨ ¬P) ↔ true :=
begin
  split,
  intro h, 
  triv, 
  intro,
  by_cases P,
  left, 
  exact h, 
  right, 
  exact h, 
end




example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  split,
  {
    intro h, 
    cases h with hP hQ, 
    {
      left, 
    exact hP,
    },
    {
      right, 
      intro hnQ,
      exfalso, 
      apply hnQ,
      exact hQ,
    },
  },
  { 
    intro h, 
    cases h with h1 h2,
    {
      left,
      exact h1,},
    {
      by_cases Q,
      right,
      exact h,
      left,
      apply h2,
      exact h,
    },
  },
end



-- 1d) add exfalso, triv, negation, by_cases
-- intro, exfalso, exact





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
