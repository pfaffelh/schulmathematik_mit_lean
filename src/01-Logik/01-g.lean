import tactic -- lade lean-Taktiken

-- Dies sind Namen für alle verwendeten Aussagen
variables (P Q R S T: Prop) 

/-
  Bisher haben wir immer ein _example_ bewiesen, ohne auf andere Ergebnisse zu verweisen. Die Mathematik lebt ja aber gerade von der Anwendung bereits bekannter Ergebnisse. Dies können wir etwa durch Anwendung der Taktiken _apply_ und _rw_ (für rewrite) erreichen. Dazu müssen wir allerdings unsere Resultate nicht mehr als _example_ formulieren, sondern als _lemma_ oder _theorem_.

  Wir führen nun zwei Lemmas l1 und l2 ein, um anschließend ein example zu beweisen. Der Taktik _rw_ gibt es dabei jeweils in zwei Versionen, und kann nur für Resultate verwendet werden, die eine Gleichheit oder ein ↔ postulieren. Bei _rw_ wird die Aussage des anzuwendenden Resultats von links nach recht, bei _rw ←_ von rechts nach linke angewendet.
-/

lemma l1 : (P → Q) ↔ (¬ Q → ¬ P) :=
begin
  split,  
  {
    intros hPQ hnQ hP,
    apply hnQ (hPQ hP),
  },
  {  
    intros h1 hP,
    by_contra h, 
    apply h1 h hP,
  },
end

lemma l2 : P ↔ ¬¬P := 
begin
  split,
  {
    intros hP hnP,
    apply hnP hP,
  },
  {
    intros h1,
    by_contra,
    apply h1 h,
  },  
end

-- Diese Aussage kennen wir bereits, und beweisen Sie nochmals neu. Diesmal verwenden wir l1 und l2 und die Taktik _rw_.
example (hPQ : P → Q) (hPnQ : P → ¬Q) : ¬P :=
begin
  intro hP,
  rw l1 at hPnQ,
  rw ← l2 at hPnQ,
  exact (hPnQ (hPQ hP)) hP,
end






