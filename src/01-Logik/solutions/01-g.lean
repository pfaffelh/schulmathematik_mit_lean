import tactic -- lade lean-Taktiken

/- 
  Am Anfang des Mathematik-Studiums lernt man die Symbole ∀ und ∃.  Diese stehen auch hier zur Verfügung. Um sie _bedienen_ zu können, brauchen wir die Taktiken _intro_, _specialize_ und _use_. 
-/

--  Wir betrachten im Folgenden logische Aussagen (Typ Prop), die von einer Variablen abhängen. Diese Variable hat wiederum einen Typ, den wir X nennen:

variable (X : Type). 

/- Um den ∃-Quantor sinnvoll nutzen zu können, müssen wir davon ausgehen dass X kein leerer Typ ist, dass es also mindestens einen Term vom Typ X gibt. Dies machen wir in den Aussagen mit der Annahma _inhabited X-. 

Um dies zu verstehen, werfen wir einen Blick in library/init/logic.lean: 
```
class inhabited (α : Sort u) :=
(default : α)
```
(Hier ist _Sort u_ eine Abkürzung für einen Typ, der auch Prop sein kann.) Dies bedeutet, dass X, falls _inhabited X_ wahr ist, ein Element hat, das _default_ heißt. Wir werden unten sehen, wie wir dieses verwenden können.

-/

-- Wir führen zunächst wieder ein paar Terme ein:
variables (P Q : X → Prop ) 
variables (R : X → X → Prop ) 
variables (S T: Prop) 

-- Wir führen zunächst den ∀-Quantor ein. Steht er in einer Aussage, so können wir mittels _intro_ einen Term des entsprechenden Typen einführen. Dies führt zu einer Situation, die wir schon kennen:

example : (∀ (x :  X), true) :=
begin
  intro x, triv,
end

-- Kommt das ∀ x in einer Hypothese h vor, so bedeutet h x die Auswertung der Hypothese für das konkrete x. 
example (inh : inhabited X) (h : ∀ x, P x) : (P default) :=
begin
  exact h default,  
end

-- Alternativ können wir die entsprechende Annahme ändern, indem wir ∀ x durch das Einsetzen eines bestimmten x ersetzen. Dies geschieht mit _specialize_
example (inh : inhabited X) (h : ∀ x, P x) : (P default) :=
begin
   specialize h default, exact h,
end
-- Übrigens ist eine einfach Möglichkeit, die alte Hypothese zu behalten, die bereits bekannte _obtain_-Taktik:
example (inh : inhabited X) (h : ∀ x, P x) : (P default) :=
begin
  obtain h1 := h default, exact h1,
end

-- Die Auflösung eines Goals mit ∃ x geschieht mit der Taktik _use_. Hier wird ein bestimmtes x verwendet, von dem man weiß, dass es der nachfolgenden Proposition genügt.
example (inh : inhabited X) (h : P default) : (∃ x, P x) :=
begin
  use default, exact h, 
end

-- Alternativ verwenden wir die Tatsache, dass es bei einer Aussage ∃ x, P x sowohl ein x geben muss, als auch P x gelten muss. Deshalb ist eine ∃-Aussage nämlich ein Produkt (bzw. logische ∧-Verknüpfung), und wir können die ⟨ , ⟩-Schreibweise verwenden:
example (inh : inhabited X) (h : P default) : (∃ x, P x) :=
begin
  exact ⟨ default, h ⟩, 
end

-- Quantoren können natürlich auch hintereinander geschaltet sein. Im folgenden Beispiel ist außerdem ∃ in einer Annahme. Diese löst man mit der _cases_-Taktik weiter auf.
example (inh : inhabited X) (h : ∃ x, ∀ y, R x y) : ∃ x, R x x :=
begin
  cases h with x h, 
  use x, exact h x,   -- oder exact ⟨ x, h x ⟩,
end

-- Aufgabe 1: Wenn P x für alle x wahr ist, dann auch für eines.
example (inh : inhabited X) : (∀ x, P x) → (∃ x, P x) :=
begin
  intro h, 
  use default, specialize h default, exact h, 
   -- oder exact ⟨ default, h default ⟩, 
end

-- Aufgabe 2: 
example (h : ∀ x, R x x) : (∀ x, ∃ y, R x y) :=
begin
  intro x, use x, exact h x, 
end

/-
  In der folgenden Aufgabe sollte man folgendes Beispiel beachten, wie man aus einer ↔-Aussage die beiden Richtungen herausholt: 
-/

example (hS : S) (hST : S ↔ T) : T :=
begin 
  exact hST.mp hS,
  -- oder exact hST.1 hS,
end

example (hT : T) (hST : S ↔ T) : S :=
begin 
  exact hST.mpr hT,
  -- oder exact hST.2 hT,
end

-- Aufgabe 3: 
example (f : X → X) (h : ∃ x, P x) (hx : ∀ x, (P x ↔ Q (f x))) : (∃ y, Q y) :=
begin
  cases h with x h, 
-- kurz:
--   exact ⟨ f x, (hx x).1 h ⟩, 
-- länger:
  use f x, apply (hx x).mp, exact h,
end

-- Aufgabe 4:
example  (h : ∀ (x : X), P x ↔ ∃ (y : X), R x y) : (∀ (y : X), ( ∀ (x : X), R x y → P x )) :=
begin
  intros y x h1, apply (h x).2, use y, exact h1, 
end

-- Es folgen ein paar Übungen, bei denen man die üblichen Regeln zur Negation von Quantoren nachrechnet. Eine Taktik, die das automatisch liefert, ist _push_neg_. Diese darf man hier jedoch nicht verwenden.

-- Aufgabe 5:
example (P : X → Prop) : (∀ (x : X), ¬P(x)) → ¬(∃ (x : X), P(x)):=
begin
  intros h1 h2, cases h2 with x h2, apply h1 x, exact h2, 
end

-- Aufgabe 6:
example (P : X → Prop) : ¬(∃ (x : X), P(x)) → (∀ (x : X), ¬P(x)) :=
begin
  intros h1 x h2, apply h1, use x, exact h2,   
end

-- Aufgabe 7: 
example (P : X → Prop) : (∃ (x : X), ¬P(x)) → ¬(∀ (x : X), P(x)) :=
begin
  intros h1 h2, cases h1 with x h1, apply h1, exact h2 x,  
end

-- Aufgabe 8
example (P : X → Prop) : ¬(∀ (x : X), P(x)) → (∃ (x : X), ¬P(x)) :=
begin
  intros h, by_contra h1, apply h, intro x,  
  have h2 : ¬¬ P x, intro h3, apply h1, use x, 
  by_contra h4, apply h2, exact h4,  
end





