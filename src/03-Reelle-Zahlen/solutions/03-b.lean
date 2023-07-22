import data.real.basic
import tactic

open classical

/-
  Das Ziel dieser Einheit ist es, die allgemein bekannte Ableitungsregel (x^(n+1))' = (n+1)*x^n herzuleiten. Hierzu benötigen wir offenbar den Begriff der Ableitung mittels eines Grenzwertes. Um die Formel herzuleiten, werden wir die Produktregel und vollständige Induktion verwenden.
-/

-- Aufgabe 1: Wir starten mit ein paar Fingerübungen:

lemma le_1 {a b c d : ℝ} (h1 : |a| ≤ b) (h2 : |c| ≤ d/b) (h3 : b > 0) : |a| * |c| ≤ d :=
begin
--  sorry,
  have h : d = b * (d/b), 
  {
    rw mul_comm,
    rw div_eq_mul_inv,
    rw [mul_assoc, mul_comm, inv_mul_cancel], simp,
    linarith,
  },
  rw h, 
  apply mul_le_mul h1 h2 (abs_nonneg c) (le_of_lt h3),
end

lemma le_2 {a b c : ℝ} (h: |a - b| ≤ c) : |a| ≤ |b| + c :=
begin
--  sorry,
  have h : | a | - | b | ≤ c, 
  apply le_trans (le_abs_self (|a| - |b|)) (le_trans (abs_abs_sub_abs_le_abs_sub a b) h),
  linarith, 
end

lemma eq_1 (a b : ℝ) (h : b ≠ 0) : a = (a / b) * b := 
begin
  exact (div_eq_iff h).mp rfl, 
end

/-
  Wir erinnern zunächst an die Definition des Grenzwertes von letztem Mal.
-/

def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

/-
  Eine Nullfolge ist eine gegen 0 konvergente Folge:
-/

def nullfolge (u : ℕ → ℝ) := limit u 0

-- Grenzwerte und Nullfolgen lassen sich inenander überführen:

lemma limit_iff_nullfolge (u : ℕ → ℝ) (l : ℝ ) : limit u l ↔ nullfolge (λ n, u n - l) :=
begin
  simp [limit, nullfolge],
end

-- Aufgabe 2: Eine Folge ist genau dann eine Nullfolge, wenn ihr Betrag eine Nullfolge ist.

lemma nullfolge_iff_abs {u : ℕ → ℝ} : nullfolge u ↔ nullfolge (λ n, |u n|) :=
begin
  split;
  {
    intro hu, intros eps heps, 
    specialize hu eps heps, 
    cases hu with N hN, 
    use N, 
    simp at *,
    exact hN, 
  },
end

-- Aufgabe 4: Es folgen nun ein paar bekannte Aussagen:
-- a) Die Summe zweier Nullfolgen ist eine Nullfolge:

lemma add_nullfolge {u v : ℕ → ℝ} (hu : nullfolge u) (hv : nullfolge v) : nullfolge (λ n, u n + v n) :=
begin
  intros eps heps,
  simp [nullfolge] at *,
  specialize hu (eps/2) (by linarith), 
  specialize hv (eps/2) (by linarith), 
  cases hu with Nu hNu, 
  cases hv with Nv hNv,
  use max Nu Nv, 
  simp at *,
  intros n hn1 hn2, 
  specialize hNu n hn1, 
  specialize hNv n hn2,
  apply le_trans (abs_add (u n) (v n)) _,
  linarith,  
end

-- b) Die Links-Multiplikation einer Nullfolge mit einer Konstanten liefert eine Nullfolge:

lemma smul_nullfolge {u : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) : nullfolge (λ n, k * (u n)) :=
begin
  by_cases h : k = 0, 
  {
    rw h, 
    simp,
    intros eps heps,
    use 1, 
    intros n hn, simp, 
    exact le_of_lt heps,  
  },
  {
    intros eps heps, 
    specialize hu (eps/|k|) _,
    refine div_pos heps _,
    apply abs_pos.2 h,
    cases hu with N hN,
    use N, 
    intros n hn, 
    simp,
    rw abs_mul,
    specialize hN n hn,
    simp at *,
    apply le_1 (by refl) hN (abs_pos.2 h),
  },
end

-- c) Die Rechts-Multiplikation einer Nullfolge mit einer Konstanten liefert eine Nullfolge:

lemma nullfolge_smul {u : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) : nullfolge (λ n, (u n) * k) :=
begin
  have h : (λ n, (u n) * k) = (λ n, k * (u n)), 
  ext, rw mul_comm,
  rw h, 
  exact smul_nullfolge hu, 
end

-- d) Die Multiplikation zweier konvergenter Folgen liefert als Grenzwert das Produkt der Grenzwerte:

lemma mul_limit {u v : ℕ → ℝ} {k l : ℝ} (hu : limit u k) (hv : limit v l) : limit (λ n, (u n) * (v n)) (k*l) :=
begin
  rw limit_iff_nullfolge, 
  have h : (λ n, u n * v n - k * l) = (λ n, (v n -l) * u n + l * (u n - k )),
  {
    ext n, ring, 
  },
  rw h, 
  clear h, 
  apply add_nullfolge,
  {
    simp [limit] at hu,
    specialize hu 1 zero_lt_one,
    cases hu with Nu hNu, 
    simp [nullfolge],
    intros eps heps,
    have h3 : eps/(|k|+1) > 0, 
    {
      apply div_pos heps,
      exact lt_add_of_le_of_pos (abs_nonneg k) zero_lt_one,  
    },
    specialize hv (eps/(|k|+1)) h3,
    cases hv with Nv hNv, 
    use max Nu Nv, 
    simp,
    intros n hn1 hn2, 
    rw abs_mul,
    specialize hNu n hn1, 
    specialize hNv n hn2, 
    have h1 : |u n| ≤ |k| + 1, 
    {
      apply le_2 hNu,  
    },
    rw mul_comm,
    apply le_1 h1 hNv _,
    exact lt_add_of_le_of_pos (abs_nonneg k) zero_lt_one, 
  },
  {
    apply smul_nullfolge,
    rw ← limit_iff_nullfolge, 
    exact hu, 
  },
end

-- e) und f) Die Multiplikation einer konvergenten mit einer Nullfolge ist eine Nullfolge:

lemma mul_nullfolge_limit {u v : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) (hv : limit v k) : nullfolge (λ n, (u n) * (v n)) :=
begin
  simp [nullfolge] at *,
  have h : 0 = 0 * k, norm_num,
  rw h, 
  exact mul_limit hu hv, 
end

lemma mul_limit_nullfolge {u v : ℕ → ℝ} {k : ℝ} (hu : limit u k) (hv : nullfolge v) : nullfolge (λ n, (u n) * (v n)) :=
begin
  have h : (λ n, (u n) * (v n)) = (λ n, (v n) * (u n)),
  ext, rw mul_comm,
  rw h, 
  exact mul_nullfolge_limit hv hu,
end

-- Stetigkeit spielt zwar im weiteren keine Rolle, aber hier wäre eine Definition:

def stetig_in (f : ℝ → ℝ) (x : ℝ) := ∀ (u : ℕ → ℝ) (hu : nullfolge u), limit (λ n, f (x + u n)) (f x)

-- Hier ist die entsprechende Definition für Differenzierbarkeit:

def diffbar_in (f : ℝ → ℝ) (x : ℝ) (l : ℝ):= ∀ (u : ℕ → ℝ) (hu1 : nullfolge u) (hu2 : ∀ n, u n ≠ 0), limit (λ n, (f (x + u n) - f x) / (u n)) l

-- Aufgabe 5: Die Identitätsfunktion ist stetig und differenzierbar:

example (x : ℝ) : stetig_in id x :=
begin
  simp [stetig_in, limit],
  intros u hu eps heps, 
  cases hu eps heps with N hN,
  use N, 
  simp at hN, exact hN,
end

lemma l1 (x : ℝ) : diffbar_in id x 1 :=
begin
--  simp [diffbar_in], 
  intros u hu1 hu2 eps heps,
--  refine ⟨1, _⟩,
  use 1, 
  intros n hn, 
  simp,
  rw div_self (hu2 n), 
  simp, 
  linarith,
end

-- Aufgaben 6 a b: Ist ein Quotient eine Nullfolge und ist der Nenner eine Nullfolge, so auch der Zähler. Bei b ist der Quotient nur konvergent.

lemma div_nullfolge' {u v : ℕ → ℝ} (hv1 : nullfolge v) (hv2 : ∀ n, v n ≠ 0) (h : nullfolge (λ n, (u n)/(v n))) : (nullfolge u) :=
begin
  intros eps heps, 
  specialize hv1 1 (by linarith),
  cases hv1 with Nv Nv1, 
  simp [nullfolge] at h, 
  specialize h eps heps,
  cases h with Nu Nu1, 
  use max Nu Nv, 
  simp at *,
  intros n hn1 hn2,
  specialize Nv1 n hn2,
  specialize Nu1 n hn1,
  specialize hv2 n, 
  rw eq_1 (|u n|) (|v n|) _,
  rw ← div_one eps at Nu1,
  rw ← abs_div, 
  rw mul_comm,
  apply le_1 Nv1 Nu1, 
  exact zero_lt_one,
  simp [hv2],
end

lemma div_nullfolge {u v : ℕ → ℝ} {k : ℝ} (hv1 : nullfolge v) (hv2 : ∀ n, v n ≠ 0) (h : limit (λ n, (u n)/(v n)) k) : (nullfolge u) :=
begin
  rw limit_iff_nullfolge at h, 
  have h1 : (λ n,  u n / v n - k) = (λ n,  (u n - v n * k)/ v n),
  {
    ext n, 
    exact div_sub' (u n) k (v n) (hv2 n),
  }, 
  rw h1 at h, 
  clear h1, 
  have h1 : nullfolge (λ (n : ℕ), (u n - v n * k)),
  apply div_nullfolge' hv1 hv2 h, 
  have h2 : nullfolge (λ n, k * (v n)),
  apply smul_nullfolge hv1, 
  have hu : u = λ n, (u n - v n * k) + (k * v n),
  ext, ring, 
  rw hu, 
  apply add_nullfolge h1 h2,
end

-- Aufgabe 7: Eine in x differenzierbare Funktion ist stetig.
lemma l0 (f : ℝ → ℝ) (x : ℝ) (hf : ∃ l : ℝ, diffbar_in f x l) : ∀ (u : ℕ → ℝ) (hu1 : nullfolge u) (hu2 : ∀ n, u n ≠ 0), limit (λ n, f (x + u n)) (f x) :=
begin
  rcases hf with ⟨l, h⟩,
  simp [diffbar_in] at h,
  intros u hu1 hu2,
  specialize h u hu1 hu2,
  rw limit_iff_nullfolge, 
  apply div_nullfolge hu1 hu2 h,
end

-- Aufgabe 8: Nun können wir die Produktregel beweisen:

lemma produktregel (f g : ℝ → ℝ) (k l x : ℝ) (hf : diffbar_in f x k) (hg : diffbar_in g x l) : diffbar_in (λ z, (f z) * (g z)) x ((f x)*l + k * (g x)) :=
begin
  intros u hu1 hu2,
  have h2 : limit (λ n, g (x + u n)) (g x),
  {
    apply l0,
    {
      use l, 
      exact hg,
    },
    {
      exact hu1, 
    },
    {
      exact hu2, 
    },
  },
  simp [diffbar_in] at *,
  specialize hf u hu1 hu2,
  specialize hg u hu1 hu2,
--  simp, 
  rw limit_iff_nullfolge, 
  have h1 : (λ n, (f (x + u n) * g (x + u n) - f x * g x) / u n - (f x * l + k * g x)) = (λ n, (f (x + u n) - (f x)) / u n * (g (x + u n) - g x ) + ((f (x + u n) - (f x)) / u n - k ) * (g x) + (f x) * ((g (x + u n) - g x) / u n - l)),
  {
    ext n, 
    calc 
    (f (x + u n) * g (x + u n) - f x * g x) /  u n - (f x * l + k * g x) =
    ((f (x + u n) - (f x)) * (g (x + u n) - g x ) + (f (x + u n) - (f x)) * (g x) + (f x) * (g (x + u n) - g x)) / u n - (f x * l + k * g x) : by {simp, rw  div_left_inj' (hu2 n), ring,}
    ... = (f (x + u n) - (f x)) / u n * (g (x + u n) - g x ) + ((f (x + u n) - (f x)) / u n - k ) * (g x) + (f x) * ((g (x + u n) - g x) / u n - l) : by {ring,},
  },
  rw h1, 
  clear h1, 
  apply add_nullfolge,
  apply add_nullfolge,
  apply mul_limit_nullfolge hf,
  rwa ← limit_iff_nullfolge, 
  apply nullfolge_smul, 
  rwa limit_iff_nullfolge at hf, 
  apply smul_nullfolge, 
  rwa limit_iff_nullfolge at hg, 
end
-- Aufgabe 9: Zu guter letzt die Aussage über die Ableitung von x ↦ x^(n+1).

example (n : ℕ) (x : ℝ) : diffbar_in (λ z, z^(n+1)) x ((n+1) * x^n) := 
begin
  induction n with d hd, 
  simp,
  exact l1 x,
  let f := λ (z : ℝ), z ^ (d + 1),
  let g := λ (z : ℝ), z,
  have h : (λ (z : ℝ), z ^ (d.succ + 1)) = (λ z, (f z) * (g z)),
  ext, 
  rw pow_succ, 
  simp [f, g], ring, 
  rw h, 
  clear h,
  let k := ((d + 1) : ℝ) * x^d,
  let l := 1, 
  have h : ((d.succ + 1) : ℝ) * x ^ d.succ = (f x) * l + k * (g x),
  simp [f, g, k, l], 
  ring, 
  rw ← pow_succ, 
  simp, 
  ring,
  rw h, 
  refine produktregel f g k l x hd _,
  simp [g], exact l1 x,
end
