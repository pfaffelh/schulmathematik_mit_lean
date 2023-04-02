import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/- 
Mit intro verwandelt man die Aussage links des ersten → in eine Hypothese und die restliche Aussage in das neue Ziel.
Stimmt ein Ziel mit einer Hypothese überein, so genügt assumption für das Schließen des Ziels. Alterantiv liefert exact den Schluss: 
 -/

example : P → P := 
begin
  intro hP, 
  assumption,
end

example : P → P := 
begin
  intro hP, 
  exact hP,
end

/- 
Ab hier folgen die Aufgaben: -/
-- Aufgabe 1) Wenn P gilt, dann folgt P aus P. 
-- Ersetzen Sie das sorry durch geeignete Befehle mit intro und exact.
example : P → (P → P):= 
begin
  intro hP1,
  intro hP2, 
  exact hP2,
end

-- Aufgabe 2) 
-- Hier beginnt der Beweis gleich mit einer Hypothese, ohne sie mit intro erzeugt zu haben.
example (hQ : Q) : (P → Q) := 
begin
  intro hP, 
  exact hQ, 
end

-- Aufgabe 3) Versuchen Sie doch mal, mit 
-- intros hP hPQ
-- anzufangen. Dies kürzt ein wenig ab.
example : P → (P → Q) → Q :=
begin
  intros hP hPQ, -- ersetzt intro hP, introhPQ 
  exact hPQ hP,
end

-- Aufgabe 4) Überlegen Sie, welche der drei folgenden examples stimmen (und warum).
example : P → Q → P :=
begin
  intros hP hQ, exact hP,
end

example : P → P → Q :=
begin
  sorry, -- stimmt nicht 
end

example : P → Q → Q :=
begin
  intros hP hQ, 
  exact hQ,
end




-- 1b) apply (refine comes later)

example (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=
begin
  exact hQR (hPQ hP),
--  apply hQR (hPQ hP), 
--  refine hQR (hPQ hP), 
--  refine hQR (hPQ _), 
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
example : (¬ P ↔ (P → false)) := 
begin
  split,
  { 
    intros h1 h2, 
    apply h1, 
    exact h2,
  },
  { 
    intro h1, 
--    change P → false, 
    exact h1, 
  }
end

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

example : false → P :=
begin
  intro h, 
  exfalso,
  exact h,
end

-- intro, triv
example : P → true :=
begin
  intro hP,
  triv, 
end

example : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,  
  intros hPQ hnQ hP,
  exact hnQ (hPQ hP),
--  apply hnQ,
--  exact hPQ hP,
  intros h1 hP,
  by_contra, 
  exact h1 h hP,
end

-- intro, by_cases, left, exact, cases, apply, exfalso
example : (P → Q) ↔ (Q ∨ ¬ P) :=
begin
  split, 
  {
    intro hPQ, 
    by_cases P,
    { 
      left, 
      exact hPQ h, 
    },
    {
      right, 
      exact h, 
    }, 
  },
  { 
    intros hPQ hP,
    cases hPQ,
    {
      exact hPQ,
    },
    {
      exfalso, 
      apply hPQ,
      exact hP,
    },
  },
end


-- 1e) add exfalso, triv, by_contra
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


-- by_contra
example : P ↔ ¬¬P := 
begin
  split, 
  intros hP hnP,
  apply hnP, exact hP,
  intro hnnP,
  by_contra, 
  apply hnnP,
  exact h, 
end

example : (P → Q) ↔ (¬Q → ¬P) := 
begin
  split, intro h, by_contra, 
end


-- 1f) refl
example : P ↔ P := 
begin
  refl,
end

example : P = P :=
begin
  refl, 
end


-- 1g) add by_cases
example : (P ∨ ¬P ) :=
begin
  by_cases P with hP hnP,
  left, exact h,
  right, exact h,
end

-- 2) have

example : P → P := 
begin
  have h : P ↔ P, refl, apply h.1,
end



-- 3) Abkürzzungen
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



























