import data.real.basic
import tactic

open classical

/-
  Das Ziel dieser Einheit ist es, die allgemein bekannte Ableitungsregel (x^(n+1))' = (n+1)*x^n herzuleiten. Hierzu benötigen wir offenbar den Begriff der Ableitung mittels eines Grenzwertes. Um die Formel herzuleiten, werden wir die Produktregel und vollständige Induktion verwenden.
-/

-- Aufgabe 1: Wir starten mit ein paar Fingerübungen:

lemma le_1 {a b c d : ℝ} (h1 : |a| ≤ b) (h2 : |c| ≤ d/b) (h3 : b > 0) : |a| * |c| ≤ d :=
begin
  sorry,
end

lemma le_2 {a b c : ℝ} (h: |a - b| ≤ c) : |a| ≤ |b| + c :=
begin
  sorry,
end

lemma eq_1 (a b : ℝ) (h : b ≠ 0) : a = (a / b) * b := 
begin
  sorry,
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
  sorry,
end

-- Aufgabe 4: Es folgen nun ein paar bekannte Aussagen:
-- a) Die Summe zweier Nullfolgen ist eine Nullfolge:

lemma add_nullfolge {u v : ℕ → ℝ} (hu : nullfolge u) (hv : nullfolge v) : nullfolge (λ n, u n + v n) :=
begin
  sorry,
end

-- b) Die Links-Multiplikation einer Nullfolge mit einer Konstanten liefert eine Nullfolge:

lemma smul_nullfolge {u : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) : nullfolge (λ n, k * (u n)) :=
begin
  sorry,
end

-- c) Die Rechts-Multiplikation einer Nullfolge mit einer Konstanten liefert eine Nullfolge:

lemma nullfolge_smul {u : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) : nullfolge (λ n, (u n) * k) :=
begin
  sorry,
end

-- d) Die Multiplikation zweier konvergenter Folgen liefert als Grenzwert das Produkt der Grenzwerte:

lemma mul_limit {u v : ℕ → ℝ} {k l : ℝ} (hu : limit u k) (hv : limit v l) : limit (λ n, (u n) * (v n)) (k*l) :=
begin
  sorry,
end

-- e) und f) Die Multiplikation einer konvergenten mit einer Nullfolge ist eine Nullfolge:

lemma mul_nullfolge_limit {u v : ℕ → ℝ} {k : ℝ} (hu : nullfolge u) (hv : limit v k) : nullfolge (λ n, (u n) * (v n)) :=
begin
  sorry,
end

lemma mul_limit_nullfolge {u v : ℕ → ℝ} {k : ℝ} (hu : limit u k) (hv : nullfolge v) : nullfolge (λ n, (u n) * (v n)) :=
begin
  sorry,
end

-- Stetigkeit spielt zwar im weiteren keine Rolle, aber hier wäre eine Definition:

def stetig_in (f : ℝ → ℝ) (x : ℝ) := ∀ (u : ℕ → ℝ) (hu : nullfolge u), limit (λ n, f (x + u n)) (f x)

-- Hier ist die entsprechende Definition für Differenzierbarkeit:

def diffbar_in (f : ℝ → ℝ) (x : ℝ) (l : ℝ):= ∀ (u : ℕ → ℝ) (hu1 : nullfolge u) (hu2 : ∀ n, u n ≠ 0), limit (λ n, (f (x + u n) - f x) / (u n)) l

-- Aufgabe 5: Die Identitätsfunktion ist stetig und differenzierbar:

example (x : ℝ) : stetig_in id x :=
begin
  sorry,
end

lemma l1 (x : ℝ) : diffbar_in id x 1 :=
begin
  sorry,
end

-- Aufgaben 6 a b: Ist ein Quotient eine Nullfolge und ist der Nenner eine Nullfolge, so auch der Zähler. Bei b ist der Quotient nur konvergent.

lemma div_nullfolge' {u v : ℕ → ℝ} (hv1 : nullfolge v) (hv2 : ∀ n, v n ≠ 0) (h : nullfolge (λ n, (u n)/(v n))) : (nullfolge u) :=
begin
  sorry,
end

lemma div_nullfolge {u v : ℕ → ℝ} {k : ℝ} (hv1 : nullfolge v) (hv2 : ∀ n, v n ≠ 0) (h : limit (λ n, (u n)/(v n)) k) : (nullfolge u) :=
begin
  sorry,
end

-- Aufgabe 7: Eine in x differenzierbare Funktion ist stetig.
lemma l0 (f : ℝ → ℝ) (x : ℝ) (hf : ∃ l : ℝ, diffbar_in f x l) : ∀ (u : ℕ → ℝ) (hu1 : nullfolge u) (hu2 : ∀ n, u n ≠ 0), limit (λ n, f (x + u n)) (f x) :=
begin
  sorry,
end

-- Aufgabe 8: Nun können wir die Produktregel beweisen:

lemma produktregel (f g : ℝ → ℝ) (k l x : ℝ) (hf : diffbar_in f x k) (hg : diffbar_in g x l) : diffbar_in (λ z, (f z) * (g z)) x ((f x)*l + k * (g x)) :=
begin
  sorry,
end
-- Aufgabe 9: Zu guter letzt die Aussage über die Ableitung von x ↦ x^(n+1).

example (n : ℕ) (x : ℝ) : diffbar_in (λ z, z^(n+1)) x ((n+1) * x^n) := 
begin
  sorry,
end
