import data.real.basic
import tactic

/-
  Heute führen wir in die reellen Zahlen ein. Dabei werden wir Grenzwerte definieren und folgenden Satz beweisen: 
  Ist A : set ℝ und x = inf A, so gibt es eine Folge a in A mit a n → x. 

  Um dies zu formulieren, benötigen wir die Definition von Infimum, sowie Grenzwerte. Mengen haben wir ja bereits letztes Mal kennengelernt.
-/

/-
  Wir beginnen mit der Menge der oberen Schranken einer Menge A.
-/

def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x}

/-- Die kleinst obere Schranke einer Menge A ist ihr Supremum. Ist dies in A selbst, so nennen wir es ihr Maximum. 
Die Aussage `is_maximum a A` means `a` ist ein Maximum von `A` -/
def is_maximum (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A

-- Aufgabe 1: Wir erinnern daran, dass x = y schon dann gilt, wenn x ≤ y und y ≤ x gilt. Dies brauchen wir gleich, um zu zeigen, dass das Maximum einer Menge eindeutig ist.
example (x y : ℝ) (hx : x ≤ y) (hy : y ≤ x) : x = y :=
begin
  exact le_antisymm hx hy, 
end

lemma unique_max (A : set ℝ) (x y : ℝ) (hx : is_maximum x A) (hy : is_maximum y A) : x = y :=
begin
  --  sorry,
  have h1 : x ≤ y, apply hy.2 x hx.1, 
  have h2 : y ≤ x, apply hx.2 y hy.1, 
  exact le_antisymm h1 h2,  
end

/-- Analog zur Menge der oberen Schranken definieren wir nun die Menge der unteren Schranken. -/
def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}

/-
  Das Infimum von A ist genau die größte untere Schranke.
-/
def is_inf (x : ℝ) (A : set ℝ) := is_maximum x (low_bounds A)

-- Aufgabe 2: Ist x das Infimum von A und x < y, so muss es ein a ∈ A geben, das zwischen x und y liegt:
lemma inf_lt {A : set ℝ} {x : ℝ} (hx : is_inf x A) : ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  intros y hy, 
  cases hx with hx1 hx2, 
  simp at *, 
  by_contra h, 
  push_neg at h, 
  specialize hx2 y h,
  linarith,
end

-- Aufgabe 3: Manchmal kann man y ≤ x nicht direkt beweisen. Wählt man jedoch ein beliebiges ε > 0 und zeige y ≤ x + ε, so ist dies äquivalent, wie wir nun zeigen.  
-- Eine Erinnerung, die eventuell hilfreich ist. Es gilt (P → Q) ↔ (¬Q → ¬P). Diese Aussage heiißt not_imp_not

lemma le_of_le_add_eps_iff {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) ↔  y ≤ x :=
begin
  split,
  {
    contrapose!, 
    -- äquivalent zu
    -- rw ← not_imp_not, 
    -- push_neg, 
    intro h, 
    use (y-x)/2, 
    split; 
    linarith, 
  },
  {
    intros h eps heps, 
    linarith, 
  }
end

/-- Wir definieren jetzt nun den Grenzwert einer Folge. limit u l bedeutet hier, dass die Folge u nach l konvergiert.  -/
def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- Aufgabe 4: Wir kombinieren jetzt die letzten beiden Aussagen: Ist y ≤ u n für alle n and x der Grenzwert von u n, dann ist y ≤ x.
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limit u x) (ineq : ∀ n, y ≤ u n) : y ≤ x :=
begin
  rw ← le_of_le_add_eps_iff, 
  intros eps heps, 
  rw [limit] at hu, 
  cases hu eps heps with N hN, 
  specialize hN N rfl.ge, 
  specialize ineq N, 
  have h : u N - x ≤ eps, exact le_of_abs_le hN,
  linarith,  
end

-- Aufgabe 5: Wir zeigen nun (fast), dass n ↦ 1/(n+1) eine Nullfolge ist. Hierzu benötigen wir eine Eigenschaft der reellen Zahlen (die aus deren Definition als Vervollständigung von ℚ folgt), dass sie ein archimedischer Körper sind; siehe die zweite Zeile des Beweises:

lemma limit_inv_succ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  intros eps heps,
  cases (archimedean_iff_nat_le.1 (by apply_instance) (1/eps)) with w hw,
  -- sorry,
  use w, 
  intros n nw, 
  apply (div_le_iff' _).2,
  rw div_le_iff heps at hw, 
  have h1 : w ≤ n+1, linarith, 
  have h2 : (w : ℝ) ≤ (n+1 : ℝ), norm_cast, exact h1, 
  have h3 : (w : ℝ)*eps ≤ (n+1)*eps, 
  exact (mul_le_mul_right heps).mpr h2,
  linarith, 
  norm_cast, 
  simp,
end

-- Aufgabe 6: Nun kommen wir zur angekündigten Aufgabe:

lemma inf_seq (A : set ℝ) (x : ℝ) :
  (is_inf x A) ↔ (x ∈ low_bounds A ∧ ∃ u : ℕ → ℝ, limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  {
    intro h, 
    split, exact h.1,
    have seq : ∀ (n : ℕ), ∃ a ∈ A, a < x + 1/(n+1 : ℝ),
    {
      intro n, 
      apply inf_lt h,  
      simp,
      norm_cast, simp,
    },
    choose u hu1 hu2 using seq,
    use u, 
    refine ⟨ _, hu1 ⟩,
    simp [limit],
    intros eps heps, 
    cases (limit_inv_succ eps heps) with N hN, 
    use N, 
    intros n Nn,
    rw abs_le, 
    split,
    simp [is_inf, is_maximum, low_bounds] at h, 
    obtain h1 := h.1 (u n) (hu1 n),
    linarith, 
    obtain h1 := hu2 n,
    obtain h2 := hN n Nn,
    linarith, 
  },
  {
    rintro ⟨ h1, u, h2, h3 ⟩,
    refine ⟨ h1, _⟩,
    simp [up_bounds], 
    intros a ha, 
    apply le_of_le_add_eps_iff.1,
    intros eps heps, 
    have h3 : ∀ n, a ≤ u n, 
    intro n, exact ha (u n) (h3 n),
    have h4: ∃ N, ∀ n ≥ N, u n ≤ x + eps,
    rcases (h2 eps heps) with ⟨N, hN⟩, 
    use N, 
    intros n Nn, 
    specialize hN n Nn, 
    rw abs_le at hN, 
    cases hN, linarith, 
    cases h4 with N hN,
    apply le_trans (h3 N) (hN N _),
    apply le_refl,
  },
end

