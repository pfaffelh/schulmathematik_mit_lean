import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/- 
  Wir verwenden nun die apply-Taktik. Ist das Ziel Q, und wir haben eine Hypothese P→Q, so können wir das Ziel schließen, wenn wir P beweisen, richtig? Mit apply führen wir diese Operation durch. 
-/
example (hP : P) (hPQ : P → Q) : Q :=
begin
  apply hPQ,
  exact hP,
end

-- Nebenbei bemerkt geht das auch so: Man setze hP in hPQ ein, genauso wie man Funktionen hintereinander ausführen kann:
example (hP : P) (hPQ : P → Q) : Q :=
begin
  exact hPQ hP,
end

-- Oft kann man übrigens apply statt exact verwenden. Der Grund ist, dass man auch hier die Hypothese auf das Ziel anwendet.
example (hP : P) : P :=
begin
  apply hP,
end

-- Aufgabe 1) Das ist fast so wie im ersten Beispiel oben, und kann entweder durch zwei Anwendungen von apply oder das Einsetzen zweier Funktionen gelöst werden:
example (hP : P) (hPQ : P → Q) (hQR : Q → R) : R :=
begin
--  apply hQR,
--  apply hPQ, 
--  exact hP,
  exact hQR (hPQ hP),
--  apply hQR (hPQ hP), 
end

-- Aufgabe 2) Ein kleines Labyrinth...
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( T → R ) :=
begin
  intro hT,
  apply hQR, 
  apply hPQ,
  apply hTP,
  assumption,  
-- oder exact hQR (hPQ (hTP hT)),
end

-- Aus dem Ziel P ↔ Q erzeugt man mit split zwei Ziele. Diese sind dann der Reihe nach abzuarbeiten:
example (hPQ : P → Q) (hQP : Q → P) : (P ↔ Q) :=
begin
  split, 
  exact hPQ,
  exact hQP,
end

-- Aufgabe 3) Dasselbe Labyrinth wie oben, aber mit einem anderen Ziel. 
example (hPQ : P → Q) (hQT : Q → T) (hQR : Q → R) (hRS : R → S) (hTP : T → P) (hRT : R → T) : ( P ↔ R )  :=
begin
  split, 
  { 
    intro hP,
    apply hQR,
    apply hPQ,
    exact hP,
  },
  { 
    intro hR,
    apply hTP,
    apply hRT,
    exact hR,
  }
end

-- Für die Negation von P, also ¬P, bemerken wir, dass ¬P definitorisch äquivalent ist zu P → false.
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
    exact h1, 
  }
end

-- Aufgabe 4) Man beachte: Ist das Ziel ¬P, so führt ein weiteres intro weiter, da das Ziel als P → false definiert ist.
example (hP : P) (hQ : Q) (hPQ : P → Q) : ¬Q → ¬ P :=
begin
  intro h1, 
  intro h2,
  apply h1, 
  apply hPQ, 
  exact hP,
end

-- Aufgabe 5) Gelten sowohl P als auch ¬P, kann etwas nicht stimmen. 
example : P → ¬P → false :=
begin
  intros h1 h2,
  apply h2, 
  exact h1,
end

