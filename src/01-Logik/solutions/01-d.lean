import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Nun kommen wir zu binären Verknüpfungen von Aussagen, also P ∧ Q bzw P ∨ Q. Diese können entweder als Hypothese auftreten, oder als Ziel. Entsprechend gibt es vier verschiedene Fälle, wie wir mit solchen Fällen umgehen können.
-/

/-
  Wir hatten bereits gesehen, dass wir bei einem Ziel P ↔ Q mit _split_ zwei Ziele für die beiden Richtungen erstellen können. Der Grund ist, dass P ↔ Q definitorisch gleich (P → Q) ∧ (Q → P) ist. Für jede solche Verknüpfung bringt uns die _split_-Taktik weiter.
-/
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split, 
  exact hP,
  exact hQ,
end

-- Aufgabe 1) Das ist ein Schritt mehr als eben...
example (hP : P) (hQ : Q) (hR : R): P ∧ (Q ∧ R) :=
begin
  split,
  {
    exact hP,
  },
  {
    split,
    {
      exact hQ,
    },
    {
      exact hR,
    }
  }
end

/-
  Bei P ∨ Q als Ziel ist es etwas anders. Hier genügt es ja, eine der beiden Aussagen (P bzw Q) zu zeigen. Entsprechend gibt es die Taktiken _left_ und _right_, je nachdem ob man das erste oder zweite Ziel verfolgt.
-/
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

-- Aufgabe 2) Wenn es drei Aussagen sind, die mit ∨ verknüpft sind, ist implizit P ∨ Q ∨ R als P ∨ (Q ∨ R) geklammert. Das sollte helfen, dieses Ziel zu erreichen:
example (hQ : Q) : P ∨ Q ∨ R :=
begin
  right, 
  left, 
  exact hQ,
end

-- Aufgabe 3) Auch geschachtelte _split_-Taktiken sind möglich.
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

/- 
  Wenn eine ∧ oder ∨ Verknüpfung in einer Hypothese vorkommt, bringt und die _cases_ Taktik weiter. 

  Bei einem ∧ in einer Hypothese entstehen so zwei Hypothesen. Da ja beide gelten müssen, ist dies identisch mit der Ausgangshypothese.
-/

example (hPQ : P ∧ Q) : P :=
begin
  cases hPQ with hP hQ, 
  exact hP,
end

/-
  Übrigens kann man in einer Hypothese h : P ∧ Q mit h.1 und h.2 direkt auf P und Q zugreifen.
-/

example (hPQ : P ∧ Q) : P :=
begin
  exact hPQ.1,
end

/-
  Ist die Hypothese h : P ↔ Q (was ja P → Q ∧ Q → P bedeutet), so kann man stattdessen auch h.mp und h.mpr anwenden: 
-/
example (hP : P) (hPQ : P ↔ Q) : Q :=
begin
  apply hPQ.mp, -- oder apply hPQ.1,
  exact hP,
end

example (hQ : Q) (hPQ : P ↔ Q) : P :=
begin
  apply hPQ.mpr,
  exact hQ,
end

/- 
  Bei einer Verknüpfung h : P ∨ Q entstehen durch _cases_ zwei Ziele. Bei einem gilt P, bei der anderen Q. Da ja unter beiden Bedingungen das Ziel erreicht werden muss, ist dies identisch mit der Ausgangshypothese.
-/
example (hPQ : P ∨ Q) : Q ∨ P :=
begin
  cases hPQ with hP hQ, 
  {
    right, 
    exact hP,
  },
  {
    left, 
    exact hQ,
  },
end

-- Aufgabe 4) Ein einfacher logischer Schluss.
example : (P ∧ Q) → (P ∨ Q) := 
begin
  intro h, 
  left, 
  cases h with hP hQ, 
  exact hP,
end

-- Aufgabe 5) P und ¬P können nicht gleichzeitig gelten...
example : (P ∧ ¬P) ↔ false :=
begin
  split,
  {
    intro h, 
    cases h with hP hnP, 
    apply hnP,
    exact hP, 
  },
  {
    intro h, 
    exfalso,
    exact h,
  },

end

-- Aufgabe 6a) eine deMorgan'sche Regel für die Negation:
example : ¬(P ∨ Q) ↔ (¬P ∧ ¬ Q) :=
begin
  split,
  {
    intro h,
    split,
    {
      intro h1,
      apply h,
      left,
      exact h1,
    },
    {
      intro h1,
      apply h,
      right,
      exact h1,
    },
  },
  {
    intros h h1,
    cases h with h2 h3,
    cases h1 with h4 h5,
    {
      apply h2,
      exact h4,
    },
    {
      apply h3,
      exact h5,
    },
  },
end


-- Aufgabe 6b) eine weitere deMorgan'sche Regel für die Negation:
example : ¬(P ∧ Q) ↔ (¬P ∨ ¬ Q) :=
begin
  split,
  {
    intro h,
    by_contra h1,
    apply h,
    split,
    { 
      by_contra h2,
      apply h1,
      left,
      exact h2, 
    },
    { 
      by_contra h2,
      apply h1,
      right,
      exact h2, 
    },
  },
  {
    intros h h1,
    cases h with h2 h3,
    {
      apply h2,
      exact h1.1,
    },
    {
      apply h3,
      exact h1.2,
    },
  },
end

-- Aufgabe 7a) Jetzt könnten wir die deMorgan'schen Regeln für ∧ und ∨ beweisen. Hier die erste:
example : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  split,
  {
    intro h,
    split,
    {
      cases h with h1 h2, 
      {
        left, 
        exact h1,
      },
      {
        right,
        exact h2.1,
      },
    },
    {
      cases h with h1 h2,
      {
        left,
        exact h1,
      },
      {
        right,
        exact h2.2,
      },
    },
  },
  {
    intro h,
    cases h with h1 h2,
    cases h1 with h3 h4,
    {
      left,
      exact h3,
    },
    {
      cases h2 with h5 h6,
      {
        left, 
        exact h5,
      },
      {
        right,
        split,
        {
          exact h4,
        },
        {
          exact h6,
        },
      },
    },
  },
end

-- Aufgabe 7b) Hier die zweite:
example : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  split,
  {
    intro h,
    cases h with h1 h2,
    cases h2 with h3 h4,
    {
      left,
      split,
      {
        exact h1,
      },
      {
        exact h3,
      },
    },
    {
      right,
      split,
      {
        exact h1,
      },
      {
        exact h4,
      },
    },
  },
  {
    intro h,
    split,
    {
      cases h with h1 h2,
      {
        exact h1.1,
      },
      {
        exact h2.1,
      },
    },
    {
      cases h with h1 h2,
      {
        left,
        exact h1.2,
      },
      {
        right,
        exact h2.2,
      },
    },    
  },
end

