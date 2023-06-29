import data.finset.basic
import tactic

open finset set
open_locale classical

variables {α β : Type*}

/-
  Das heutige Ziel ist der Beweis des (endlichen) Schubfachprinzips. Verteilt man m Kugeln auf n Schubfächer, so dass in keinem Schubfach mehr als eine Kugel ist, so muss m ≤ n sein. 
  Anders ausgedrückt: Ist n < m, so landen mindestens zwei Kugeln im gleichen Schubfach. 
  Etwas mathematischer ausgedrückt: Ist |K| = m und |S| = n mit n < m, so gibt es keine injektive Abbildung K → S. 

  Um dies zu formulieren, benötigen wir (endliche) Mengen und Injektivität.
-/

/-
  Auch in Lean gibt es Mengen. Für diese gibt es Rechensymbole wie ∈ und ⊆. Dabei bedeutet A ⊆ B dasselbe wie ∀ x, x ∈ A → x ∈ B.  Eine Menge kann man dabei etwa {x | P x} durch P : α → Prop  definieren:
-/

example (A : set α) (P : α → Prop) (y : α): y ∈ { x | P x} ↔ P y :=
begin
  refl, 
end

/-
  Mit anderen Worten ist set α und α → Prop definitorisch gleich. 

  Noch ein wichtiger Trick: Da A ⊆ B dasselbe ist wie x ∈ A → x ∈ B, kann man ein Goal x ∈ B mittels _apply_ umwandeln. 
-/

example (A B : set α) (h : A ⊆ B) (x : α) (hx : x ∈ A) : x ∈ B :=
begin
  apply h, 
  assumption,
end

-- Aufgabe 1: Es sollte klar sein, dass ∩ eine entsprechende ∧-Verknüpfung ist und ∪ eine ∨-Verknüpfung. Hier eine einfache Aufgabe dazu. 

example (A B C : set α) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C :=
begin
  intros x hx, 
  sorry,
end

/-
  Mengen definieren auch Subtypen. Das bedeutet, dass A : set α nicht nur eine Menge ist, sondern ein Subtyp, d.h. man kann x : A schreiben. Dabei ist x = ⟨x.val, x.prop⟩, also ein Paar, das aus einem x.val : α und einem x.prop : α → Prop besteht. 
-/

example (A : set α) (x : A) : (x.val ∈ A) :=
begin
  exact x.prop,
end

example (A : set α) (x : A) (P : α → Prop) (hA : A = {x | P x}) : P = λ x, x ∈ A :=
begin
  ext x, 
  rw hA, 
  refl,
end

/-
  Zwei Terme x y : A sind dabei genau dann gleich, wenn ihre Werte übereinstimmen. Beide sind ja sowieso in A.
-/

example (A : set α) (x y : A) : x.val = y.val → x = y :=
begin
  exact subtype.ext,
end

/-
  Injektivität ist ein wichtiges Konzept. Es ist folgendermaßen definiert:

  def injective (f : α → β) : Prop := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
-/

-- Aufgabe 2: Die Komposition zweiter injektiver Abbildungen ist injektiv:
example (f g : α → α) (hf : function.injective f) (hg : function.injective g) : function.injective (λ x, f (g x)) := 
begin
  sorry,
end

-- Aufgabe 3:
example (A B : set α) (f : A → B) (hf : function.injective f) : function.injective (λ x, (f x).val) :=
begin
  sorry,
end

/-
  Es gibt nicht nur set, sondern auch finset. Dabei ist A : finset α eine endliche Teilmenge von α, und damit auch eine Teilmenge von α. Diese werden wir weiter unten brauchen. 
  
  Ist A : finset α und x : α, so entsteht insert x A : finset α durch Einfügen von x in A. (Es kann dabei sein, dass x ∈ A ist, dann ist A = insert x A.)

  Dabei gelten folgende zwei Aussagen:

  finset.mem_insert_of_mem : ∀ {α : Type u_1} [_inst_1 : decidable_eq α] {s : finset α} {a b : α}, a ∈ s → a ∈ insert b s

  finset.mem_insert_self : ∀ {α : Type u_1} [_inst_1 : decidable_eq α] (a : α) (s : finset α), a ∈ insert a s

-/

-- Aufgabe 4: Wenn eine Funktion f : (insert x A) → B) injektiv ist, so auch die Einschränkung auf A:

example {A B : finset α} {x : α} (f : (insert x A) → B) (hf : function.injective f) : function.injective (λ (a : A), f ⟨a, mem_insert_of_mem a.prop⟩) :=
begin
  sorry,
end



/- Aufgabe 5: Wir kommen nun zum angesprochenen Schubfachprinzip. 

Ein möglicher (aber nicht der einzige) Beweis verwendet die finset-Induktion:

finset.induction_on : ∀ {α : Type u_1} {p : finset α → Prop} [_inst_2 : decidable_eq α] (s : finset α), p ∅ → (∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) → p s
-/



lemma schubfachprinzip (A : finset α) (B : finset β) (hcard : B.card < A.card) : ¬ (∃ (f : A → B), function.injective f) :=
begin
  sorry,
end







