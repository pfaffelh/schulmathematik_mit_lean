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
  { 
    left, 
    use 0, 
    simp,
  },
  {
    cases hd with h1 h2,
    { 
      right, 
      cases h1 with m h3, 
      use m, 
      rw h3,
    },
    { 
      left, 
      cases h2 with m h3, 
      { 
        use (m+1), 
        rw h3, 
        ring,
      },
    },
  },
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
  induction n with d hd, 
  {
     simp, 
  },  
  {
    rw pow_succ, 
    split,
    {
      intro h, 
      by_contra h1,
      rw ← not_iff_not at hd,
      simp at *,
      obtain h3 : 1 < a * a ^ d.succ := one_lt_mul (le_of_lt h1) (hd.2 h1),
      linarith, 
    },
    {
      intro h1, 
      apply mul_le_one h1 (pow_nonneg h (succ d)) (hd.2 h1),
    },
  },
end

-- Aufgabe 3: Es folgt eine Aufgabe aus Analysis 1, nämlich 1 + nx ≤ (1+x)^n. Dies gilt für -1 ≤ x. Sollte das zu schwer sein, ändern Sie doch die Annahme h in 0 ≤ x. 
-- Hier ein paar Aussagen, die vielleicht hilfreich sind (gehen Sie jeweils ans Ende der Zeile, um die Aussage im rechten Teil zu sehen):

#check @ add_mul
#check @ add_assoc
#check @ mul_le_mul_of_nonneg_left
#check @ mul_nonneg
#check @ mul_le_mul_left
#check @ le_trans

example (n : ℕ) (x : ℝ) (h : -1 ≤ x) : (1 : ℝ) + n*x ≤ (1+x)^n :=
begin
  induction n with d hd, 
  {
    simp, 
  },
  {
    simp, 
    rw pow_succ, 
    rw add_mul, 
    rw ← add_assoc, 
    rw add_mul, 
    simp, 
    have h1 : x ≤ x * (1+x)^d, 
    {
      by_cases hx : 0 ≤ x, 
      {
        nth_rewrite 0 ← mul_one x, 
        apply mul_le_mul_of_nonneg_left _ hx,
        have h2 : 1 ≤ 1 + (d : ℝ) * x, 
        { 
          simp, 
          have h3 : (d : ℝ) ≥ 0, { simp, },
        exact mul_nonneg h3 hx,
        },
        exact le_trans h2 hd,
      },
      {
        simp at hx, 
        rw ← neg_le_neg_iff, 
        obtain h1 : 0 < -x, by linarith, 
        rw ← neg_mul, 
        obtain hx2 : 1+x ≥0, by linarith,  
        have h2 : (1+x)^d ≤ 1, 
        {
          cases d with d hd1, 
          { simp, },
          {
            rw l0 (1+x) (d) hx2, 
            linarith, 
          },
        },
        nth_rewrite 1 ← mul_one (-x), 
        exact (mul_le_mul_left h1).mpr h2, 
      },
    },
    linarith, 
  },
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
    dsimp [P],
    intro h0, 
    use 0, 
    simp, 
    assumption, 
  },
  have ind_step : ∀ (k : ℕ), (∀ (m : ℕ), m ≤ k → P m) → P (k + 1),
  {
    dsimp [P],
    intros k h1,
    by_cases h : ∃ (l : ℕ) (h : l ∈ S), l ≤ k, 
    {
      rcases h with ⟨ l, hl, hl1 ⟩, 
      intro h2,  
      exact h1 l hl1 hl,
    },
    {
      push_neg at h, 
      intro h2,
      use k+1, 
      refine ⟨h2,_⟩,
--      split, exact h2, 
      intros m hm,
      have h3 : k < m → k+1 ≤ m, 
      { exact succ_le_iff.mpr,  },
      apply h3, 
      apply h m hm,
    },
  },
  intro d, 
  apply nat.case_strong_induction_on d base ind_step,
end



