import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Wir kommen nun zu ein paar abkürzende Taktiken, nämlich _rintros_, _rcases_ und _obtain_. Hierzu sind zunächst zwei Klammer-Schreibweisen wichtig, nämlich _⟨ hP, hQ ⟩_ und _(hP | hQ)_. Die erste Schreibweise steht für die gleichzeitige Einführung von _hP und _hQ_, die zweite für zwei Goals, eine mit _hP_, die andere mit _hQ_. (Also genau wie bei der _cases_-Taktik. Allerdings ist es hier so, dass wir auch mehr als zwei Terme verarbeiten können, also etwa _⟨ hP, hQ, hR ⟩_ für eine gemeinsame Einführung von _hP_, _hQ_ und _hR_. Es ist auch möglich, zu schachteln, also etwa _⟨ (hP | hQ), hR ⟩_ ). 

  Die drei Taktiken sind Abkürzungen, nämlich _rintros_ für _intros_ + _cases_, _rcases_ für eine flexiblere Version von _cases_, und _obtain_ für _intros_ + _have_. Wir starten mit Beispielen.
-/

-- Ein Beispiel mit rintros
example : (P ∨ Q) → (¬Q → P) := 
begin
  rintros (hP | hQ) h,
-- identisch mit
--   intros h1 h,
--   cases h1 with hP hQ,
  {
    exact hP,
  },
  {
    exfalso, 
    exact h hQ, 
  },
end

-- Ein Beispiel mit rcases
example (h : P ∧ Q ∧ R) : (P ∨ Q ∨ R) :=
begin
  rcases h with ⟨ hP, hQ, hR ⟩,
  -- identisch mit
  -- cases h with hP hQR,
  -- cases hQR with hQ hR,
  left, 
  exact hP,
end

-- Ein Beispiel mit obtain
example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  obtain ⟨ hQ, hnQ ⟩ := ⟨ hPQ hP, hPnQ hP ⟩,
  exact hnQ hQ,
end

/-
  Wir bemerken, dass wir die Schreibweise mit ⟨ P, Q⟩ und (P | Q) auch bei anderen Taktiken anwenden können.
  -/

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  exact ⟨hP, hQ⟩, 
end

-- Aufgabe 1) Dies kann man nun in einer einzigen Zeile erledigen.
example (hR : R) (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( Q ∧ T) :=
begin
  sorry,
end

-- Aufgabe 2) Hier ist rintro hilfreich. 
example (h : P → Q → R → S) : (P ∧ Q ∧ R) → S :=
begin
  sorry,
end

-- Aufgabe 3) Hier auch...
example : (P ∨ Q) → (¬Q → P) := 
begin
  sorry,
end

-- Aufgabe 4) Noch einmal...
example : (P → Q) ∧ (Q → R) → (P → R) := 
begin
  sorry,
end
