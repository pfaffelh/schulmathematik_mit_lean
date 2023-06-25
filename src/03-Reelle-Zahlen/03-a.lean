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
  sorry,
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
  sorry,
end

-- Aufgabe 3: Manchmal kann man y ≤ x nicht direkt beweisen. Wählt man jedoch ein beliebiges ε > 0 und zeige y ≤ x + ε, so ist dies äquivalent, wie wir nun zeigen.  
-- Eine Erinnerung, die eventuell hilfreich ist. Es gilt (P → Q) ↔ (¬Q → ¬P). Diese Aussage heiißt not_imp_not

lemma le_of_le_add_eps_iff {x y : ℝ} : (∀ ε > 0, y ≤ x + ε) ↔  y ≤ x :=
begin
  sorry,
end

/-- Wir definieren jetzt nun den Grenzwert einer Folge. limit u l bedeutet hier, dass die Folge u nach l konvergiert.  -/
def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- Aufgabe 4: Wir kombinieren jetzt die letzten beiden Aussagen: Ist y ≤ u n für alle n and x der Grenzwert von u n, dann ist y ≤ x.
lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : limit u x) (ineq : ∀ n, y ≤ u n) : y ≤ x :=
begin
  sorry,
end

-- Aufgabe 5: Wir zeigen nun (fast), dass n ↦ 1/(n+1) eine Nullfolge ist. Hierzu benötigen wir eine Eigenschaft der reellen Zahlen (die aus deren Definition als Vervollständigung von ℚ folgt), dass sie ein archimedischer Körper sind; siehe die zweite Zeile des Beweises:

lemma limit_inv_succ : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, 1/(n + 1 : ℝ) ≤ ε :=
begin
  sorry,
end

-- Aufgabe 6: Nun kommen wir zur angekündigten Aufgabe:

lemma inf_seq (A : set ℝ) (x : ℝ) :
  (is_inf x A) ↔ (x ∈ low_bounds A ∧ ∃ u : ℕ → ℝ, limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  sorry,
end

