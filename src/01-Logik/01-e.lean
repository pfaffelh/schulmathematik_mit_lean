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
  sorry,
end

-- Aufgabe 2) Irgendwann muss man hier danach sehen, ob Q gilt oder nicht...

example : (P ∨ Q) ↔ (P ∨ (¬Q → P)) := 
begin
  sorry,
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
  sorry,
end

-- Aufgabe 4) Auch hier kann have_ helfen.
example (hPQ : P → Q) (hQR : Q → R ) (hSR : S → R ) : (P → R) ∧ (S → R):= 
begin
  have h : P → R, 
  sorry,
end


-- Aufgabe 5) Die folgende Aufgabe fand ich nicht einfach zu beweisen. Man erinnere sich daran, dass P → Q identisch ist mit Q ∨ ¬P. Mit einigen Anwednungen von _have_ sollte es aber gehen.

example : (((P → Q) → P) → P) := 
begin
  sorry,
end






