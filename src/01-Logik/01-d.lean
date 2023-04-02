import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Nun kommen wir zu binären Verknüpfungen von Aussagen, also P ∧ Q bzw P ∨ Q. Diese können entweder als Hypothese auftreten, oder als Ziel. Entsprechend gibt es vier verschiedene Fälle, wie wir mit solchen Fällen umgehen können.
-/

/-
  Wir hatten bereits gesehen, dass wir bei einem Ziel P ↔ Q mit split zwei Ziele für die beiden Richtungen erstellen können. Der Grund ist, dass P ↔ Q definitorisch gleich (P → Q) ∧ (Q → P) ist. Für jede solche Verknüpfung bringt uns die split-Taktik weiter.
-/
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split, 
  exact hP,
  exact hQ,
end

example (hP : P) : P ∨ Q :=
begin
  left, 
  exact hP,
end

example (hQ : Q) : P ∨ Q :=
begin
  right,
  exact hQ,
end


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
