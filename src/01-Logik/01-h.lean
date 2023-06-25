import tactic -- lade lean-Taktiken

/- 
  Wir lernen hier noch ein paar Taktiken kennen, die im folgenden wichtig sein werden. Insgesamt bewegen wir uns weiter im Rahmen des letzten Blattes und betrachten folgendes Szenario:
-/

variables (X Y : Type) [inhabited X] 
variables (P Q : X → Prop ) 
variables (R : X → X → Prop ) 
variables (S T: Prop) 

/-
  Wir starten einfach und beweisen x = x. Die Gleichheit eines Terms mit sich selbst (bzw. einem Term, der definitorisch identisch ist). Dies ist die _refl_-Taktik.
-/

example (x : X) : x = x :=
begin
  refl,
end

-- Aufgabe 1: Geht zwar auch ohne refl, aber mit ist es schneller...
example (P : Prop) : ¬P ↔ (P → false) :=
begin
  sorry,
end

/-
  Die mathlib ist ja schon voll mit Aussagen. Um diese zu durchsuchen, gibt es die Taktiken _library_search_ und _suggest_; siehe Skript. Hier ein Beispiel:
-/

example (P Q : Prop) : ((P → Q) ∧ (Q → P)) ↔ (P ↔ Q) :=
begin
  -- library_search, liefert
  exact iff_def.symm,
end

/- 
  Eine weitere Taktik werden wir noch oft brauchen: _rw_ (für rewrite); siehe das Skript. Hier ein Beispiel:
-/

example (x y z : X) : (x = y) → (y = z) → (x = z) :=
begin
  intros h1 h2, 
  rw h1, 
  rw h2, 
end

-- Was ist hier wohl der Unterschied zum letzten Beweis?
example (x y z : X) : (x = y) → (y = z) → (x = z) :=
begin
  intros h1 h2, 
  rw ← h2,
  rw h1, 
end

-- Die rw-Taktik funktioniert sowohl mit =-Aussagen, als auch mit ↔-Aussagen. Beweisen wir zunächst eine ↔-Aussage:
lemma l1 (P Q : Prop ) : (P → Q) ↔ (Q ∨ ¬P ):=
begin
  split,
  {
    intro hPQ, 
    by_cases P, 
    {
      left, exact hPQ h, 
    },
    { 
      right, exact h, 
    },
  },
  intros h hP,
  cases h with h1 h2, 
  {
    exact h1, 
  },
  {
    exfalso, exact h2 hP,
  }, 
end

-- Aufgabe 2: Nun kann man l1 verwenden (mittels rw), um die schwierige Aufgabe aus 01-e zu lösen; push_neg kann auch hilfreich sein...
example (P Q : Prop): (((P → Q) → P) → P) := 
begin
  rw l1, 
  sorry,
end

-- Aufgabe 3: 
-- Hier kann man zwar direkt library_search verwenden, aber wir wollen nun l1 von oben (mit rw) verwenden. Schaffen Sie das?
lemma l2 (P Q : Prop ) : (P → Q) ↔ (¬Q → ¬P) :=
begin
  rw l1 P Q, 
  sorry,
end

/-
  Wir kommen nun noch dazu, Funktionen zu definieren und brauchen dazu eine Notation, die äquivalent ist zu f : ↦ f x (wobei f x die lean-Schreibweise für f(x) ist; Informatiker sind manchmal sparsam mit Klammern...) Die geschieht mit "λ": Der Ausdruck
  λ x, 2*x
  ist die Funktion x ↦ 2*x. Hier zwei Beispiele:
-/

example : (∃ (f : X → X), true) :=
begin
  use λ x, default, 
end

/-
  Will man im letzten Beispiel der Funktion einen expliziten Namen geben, so geht das so:
-/

example : (∃ (f : X → X), true) :=
begin
  let f : X → X := λ x, default, 
  use f, 
end

-- Noch ein Beispiel:
example (f g : X → Prop) : ∃ (h : X → Prop), ∀ x, h x = (f x ∧ g x) :=
begin
  use λ x, f x ∧ g x, 
  intro x, 
  refl,
end

-- Aufgabe 4: Hier kann man die Funktionen f unf g am besten explizit angeben.
example : ∃ (f g : X → Prop), ∀ x, (f x) ↔ ¬(g x) :=
begin
  sorry, 
end

-- Aufgabe 5: Noch ein Hinweis, den wir oft verwenden werden. Gehen Sie doch mal mit dem Cursor auf das xor und drücken F12. Dann werden Sie zur Definition von xor geführt. Dann ist die Aufgabe nicht schwerer als die letzte.
example : ∃ (f g : X → Prop), ∀ x, xor (f x) (g x) :=
begin
  sorry,
end

-- Aufgabe 6: Hier können Sie entweder library_search verwenden, oder Sie schaffen es, mathlib so gut zu verstehen, dass Sie einen eigenen Beweis hinbekommen.
example : (∀ (x : X), ∃ (y : X), R x y) → ∃ (f : X → X), ∀ (x : X), R x (f x) :=
begin
  sorry,
end

/-
  Wann sind zwei Funktionen f und g eigentlich gleich? In Lean ist das genau dann der Fall, wenn alle Funktionswerte an allen Stellen gleich sind. (Vorsicht: Um überhaupt behaupten zu können, dass f = g gilt, müssen beide Funktionen denselben Typ haben, d.h. Definitions- und Bildmenge müssen übereinstimmen.) Um aus dem Goal f = g das Goal zu machen, dass f und g an allen Punkten übereinstimmen, gibt es die _ext_-Taktik.
-/

example (f g : X → Prop) (h : ∀ x, f x = ¬¬(g x)) : f = g :=
begin
  ext, 
  rw (h x), 
  rw not_not,
end

-- Aufgabe 7: Mit dem obigen Beispiel sollte das einfach sein.
example (f g : X → Y) : (∀ x, ((f x) = (g x))) ↔ f = g :=
begin
  sorry,
end

/-
  Hier noch eine hilfreiche Taktik: _change_. Diese ändert das Goal bzw. eine Aussage in eine definitorisch identische Aussage:
-/

example (x : X) (f : X → Prop) : (¬(f x)) = ((f x) → false) :=
begin
  change (¬(f x)) = (¬(f x)),
  refl,
end

-- Aufgabe 8: Hier ist die rechte Seite eine Version zu sagen, dass Y nur ein Element enthält.
example : (∀ (f g : X → Y), f = g) → (∀ (y1 y2 : Y), y1 = y2) :=
begin
  sorry,
end
