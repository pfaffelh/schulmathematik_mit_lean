import tactic -- lade lean-Taktiken
import data.real.basic
open nat finset

/-
  Wir kommen nun zur vollständigen Induktion. Diese ist so ähnlich wie cases n für n : ℕ aus 02-a.lean.
-/

-- Wiederholung von 02-a.lean:
example (n : ℕ) : n=0 ∨ (∃ (k : ℕ), n = succ k) :=
begin
  cases n, 
  left, refl,
  right, use n, 
end

-- Mit vollständiger Induktion gibt es noch die Induktionsannahme, aber der Beweis ist identisch: Die Syntax der Induktions-Taktik ist _induction n with d hd_, wobei das eine Induktion über n ist, und die Variable in d umbenannt wird und hd die Induktionshypothese ist.

example (n : ℕ) : n=0 ∨ (∃ (k : ℕ), n = succ k) :=
begin
  induction n with d hd, 
  left, refl,
  right, use d,
end

-- Aufgabe 1) Hier eine erste Aufgabe. Wir erinnern daran, dass man eine Hypothese h : P ∨ Q mittels _cases h with hP hQ_ in zwei Goals auflösen kann.

example (n : ℕ) : (∃ (k : ℕ), n = 2*k) ∨ (∃ (k : ℕ), n = 2*k+1) :=
begin
  induction n with d hd, 
  left, 
  use 0, simp,
  cases hd with hd1 hd2, 

  sorry,
  sorry,
end

-- Aufgabe 2: Eine nicht-negative reelle Zahl a ist genau dann ≤ 1, wenn a^n ≤ 1. Dies ist mittels Induktion zu beweisen.
/-
  Folgende Aussagen kommen in meinem Beweis vor:

pow_succ : ∀ {M : Type} [_inst_1 : monoid M] (a : M) (n : ℕ), a ^ (n + 1) = a * a ^ n

not_iff_not : ∀ {a b : Prop}, ¬a ↔ ¬b ↔ (a ↔ b)

one_lt_mul : ∀ {α : Type} [_inst_1 : ordered_semiring α] {a b : α}, 1 ≤ a → 1 < b → 1 < a * b

le_of_lt : ∀ {α : Type} [_inst_1 : preorder α] {a b : α}, a < b → a ≤ b

pow_nonneg : ∀ {α : Type} [_inst_1 : ordered_semiring α] {a : α}, 0 ≤ a → ∀ (n : ℕ), 0 ≤ a ^ n

mul_le_one : ∀ {α : Type} [_inst_1 : ordered_semiring α] {a b : α}, a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1

-/

lemma l0 (a : ℝ) (n : ℕ) (h : 0 ≤ a) : a^(n+1) ≤ 1 ↔ a ≤ 1 :=
begin
  sorry,
end

-- Aufgabe 3: Es folgt eine Aufgabe aus Analysis 1, nämlich 1 + nx ≤ (1+x)^n. Dies gilt für -1 ≤ x. Sollte das zu schwer sein, ändern Sie doch die Annahme h in 0 ≤ x. 
-- Hier ein paar Aussagen, die vielleicht hilfreich sind (gehen Sie jeweils ans Ende der Zeile, um die Aussage im rechten Teil zu sehen):

#check @ add_mul
#check @ add_assoc
#check @ mul_le_mul_of_nonneg_left
#check @ mul_nonneg
#check @ mul_le_mul_left
#check @ le_trans

example (x : ℝ) (d : ℕ): 0 ≤ (d : ℝ)*x^2 :=
begin
  obtain h : d ≥ 0, exact zero_le d,
  have h1 : (0 : ℝ) = d*0, simp,
  rw h1, 
  apply mul_le_mul_of_nonneg_left,
  nlinarith, exact cast_nonneg d, 
end


example (n : ℕ) (x : ℝ) (h : 0 ≤ x) : (1 : ℝ) + n*x ≤ (1+x)^n :=
begin
  induction n with d hd, 
  simp,
--  rw pow_succ, 
   have hd2 : (1+x)*(1 + d*x) ≤ (1+x)^(d+1),
  apply mul_le_mul_of_nonneg_left hd, 
  linarith, 
  have hd3 : (1 : ℝ) + (d+1)*x ≤ (1+x) * (1+d*x), 
  rw mul_add, simp,rw add_mul, rw ←  add_assoc, simp, ring, 
  sorry,
end



-- Neben der üblichen (schwachen) Induktion gibt es noch die starke Induktion. Hier darf man bei der Induktionsannahme die zu beweisende Aussage nicht nur für ein d verwenden, sondern für alle k ≤ d. Die entsprechende Aussage der mathlib ist

#check @ case_strong_induction_on

-- Diese starke Induktion verwenden wir nun.

-- Aufgabe 4: Hier ist der Wohlordnungssatz für die natürlichen Zahlen. Jede nicht-leere Menge natürlicher Zahlen enthält eine kleinste Zahl.

example (S : set ℕ) (h : S.nonempty) : ∃ (n : ℕ) (h : n ∈ S), ∀ m ∈ S, n ≤ m :=   
begin
  cases h with d hd,
  let P := λ k, k ∈ S → ∃ (n : ℕ) (h : n ∈ S), ∀ m ∈ S, n ≤ m,
  revert d hd, 
  change ∀ (a : ℕ), P a, 
  have base : P 0,
  {
    sorry,
  },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  {
    sorry,
  },
  intro d, 
  apply nat.case_strong_induction_on d base ind_step,
end



