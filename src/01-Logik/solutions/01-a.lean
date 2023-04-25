import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T : Prop) 

/- 
Mit _intro_ verwandelt man die Aussage links des ersten → in eine Hypothese und die restliche Aussage in das neue Ziel.
Stimmt ein Ziel mit einer Hypothese überein, so genügt _assumption_ für das Erreichen des Ziels. Alterantiv liefert _exact_ den Schluss: 
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
-- Ersetzen Sie das _sorry_ durch geeignete Befehle mit _intro_ und _exact_.
example : P → (P → P):= 
begin
  -- sorry,
  intro hP1,
  intro hP2, 
  exact hP2,
end

-- Aufgabe 2) 
-- Hier beginnt der Beweis gleich mit einer Hypothese, ohne sie mit _intro_ erzeugt zu haben.
example (hQ : Q) : (P → Q) := 
begin
  intro hP, 
  exact hQ, 
end

-- Aufgabe 3) Versuchen Sie doch mal, mit 
-- _intros hP hPQ_
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


