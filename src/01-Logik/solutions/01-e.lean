import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Bisher haben sich die verwendeten Hypothesen immer durch Umformung bereits vorhandener Hypothesen ergeben. Das muss aber keineswegs immer so sein, weil man ja neue Hypothesen hinzufügen kann, die man aber auch beweisen muss. Wir lernen hier _by_cases_ und _have_ kennen.
-/

/-
  Die _by_cases_-Taktik nutzt das "Gesetz des ausgeschlossenen Dritten". Übersetzt heißt das, dass jede Aussage entweder wahr oder falsch ist (und es keine dritte Möglichkeit gibt). Mit by_cases h : P wird die Hypothese h : P ∨ ¬P hinzugefügt und das Ergebnis von cases h angezeigt.
-/

example : (P ∨ ¬P) :=
begin
  by_cases h : P,
  {
    left, 
    exact h, 
  },
  {
    right, 
    exact h, 
  }, 
end

-- Aufgabe 1) Wenn Q sowohl aus P als auch aus ¬P folgt, sollte Q immer gelten.

example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q :=
begin
  by_cases P,
  exact hPQ h, 
  exact hnPQ h,  
end

-- Aufgabe 2) Irgendwann muss man hier danach sehen, ob Q gilt oder nicht...

example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  split,
  {
    rintro (hP | hQ), 
    {
      left, exact hP,
    },
    {
      right,  
      intro hnQ,
      exfalso, 
      exact hnQ hQ,
    },
  },
  { 
    rintro (h1 | h2), 
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


/-
  Das folgende Beispiel ist recht knapp gelöst, die _exact_-Zeile ist jedoch zunächst recht schwer zu lesen. 
  -/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  exact (hPnQ hP) (hPQ hP),
end

/-  
  Einfacher lesbar wäre es, wenn wir zunächst Q und anschließend ¬Q zeigen würden. Die machen wir mit der _have_-Taktik. Hiermit können wir beliebige neue Hypothesen postulieren, die wir ersteinmal beweisen müssen, bevor sie zur Verfügung stehen. 
-/

example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  have hQ : Q, 
  {
    apply hPQ hP,
  },
  have hnQ : ¬Q,
  {
    apply hPnQ hP,
  },
  exact hnQ hQ,
end

-- Aufgabe 3) Wir können hier by_cases P mittels _have_ umgehen. 
example (hPQ : P → Q) (hnPQ : ¬P → Q) : Q :=
begin
  have h : P ∨ ¬ P → Q, 
  {
    intro h1,
    cases h1 with h2 h3,
    {
      exact hPQ h2,
    },
    {
      exact hnPQ h3,
    },
  },
  {
    apply h,
    exact em P,
  },
end

-- Aufgabe 4) Auch hier kann have_ helfen.
example (hPQ : P → Q) (hQR : Q → R ) (hSR : S → R ) : (P → R) ∧ (S → R):= 
begin
  have h : P → R, 
  {
    intro hP,
    apply hQR (hPQ hP),
  },
  exact ⟨ h, hSR ⟩,
end


-- Aufgabe 5) Die folgende Aufgabe fand ich nicht einfach zu beweisen. Man erinnere sich daran, dass P → Q identisch ist mit Q ∨ ¬P. Mit einigen Anwednungen von _have_ sollte es aber gehen.

example : (((P → Q) → P) → P) := 
begin
  intro h,
  have h1 : P ∨ (¬Q ∧ P),
  {
    by_cases h1 : P,
    {
      left, exact h1,
    },
    {
      left, 
      have h2 : P → Q,
      {
        intro hP, 
        exfalso, 
        exact h1 hP,
      },
      apply h,
      exact h2,    
    },
  },
  cases h1 with h3 h4,
  exact h3,
  exact h4.2,
end






