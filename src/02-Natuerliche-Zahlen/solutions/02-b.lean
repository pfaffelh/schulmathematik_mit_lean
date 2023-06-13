import tactic -- lade lean-Taktiken
open int nat has_dvd

/-
  Teilbarkeit ist seit der Grundschule ein Thema im Mathematik-Unterricht. Wir verwenden diese hier gleich für ℤ, damit wir keine Probleme mit Subtraktionen bekommen. Der Anfang ist einfach. Man beachte, dass nach _simp [dvd]_ die Definition der Teilbarkeit sichtbar wird. Es ist eine ∃-Aussage! 
-/

example : (5 : ℤ) ∣ 10 :=
begin
  simp [dvd], 
  use 2, 
  norm_num,
end

/- Aufgabe 1: 
  Etwas schwieriger ist es zu zeigen, dass etwas nicht teilbar ist. Hier ist es hilfreich, eine Strategie zurechtzulegen: Angenommen, 5 wäre durch 9 teilbar. Dann müsste es doch ein a : ℤ geben mit 5*a=9. Einerseits müsste 1 < a sein, denn 5*1=5<9. Andererseits müsste a < 2 sein, denn 5*a = 9 < 10 = 5*2. Aus diesen Überlegungen (und einigen Anwendungen von _linarith_, was Ungleichungen lösen kann, lässt sich diese Nicht-Teilbarkeit beweisen.)
-/

example : ¬(5 : ℤ) ∣ 9 :=
begin
  intro h, 
  cases h with a h, 
  have h1 : 1 < a, 
  {
    by_contra h1, push_neg at h1, 
    have h2 : 9 ≤ 5, linarith, linarith,   
  }, 
  have h2 : a < 2, 
  {
    by_contra h2, push_neg at h2, 
    have h3 : 10 ≤ 9, linarith, linarith,   
  },
  linarith, 
end

/-
  Es folgen nun ein paar Aufgaben, die jeweils auf zwei Arten und Weisen lösbar sind: Entweder man verwendet einfach library_search (und clickt dann auf die Lösung auf der rechten Seite) oder -- was auch nicht schwer ist -- löst die Aufgaben "per Hand". Auf jeden Fall sollte man sich jedoch für die Aufgaben weiter unten merken, was die jeweiligen Aussagen sind. Diese werden wir noch brauchen. 
-/

-- Aufgabe 2a
example (n : ℤ) : n ∣ n :=
begin
  -- exact dvd_refl n,
  use 1, simp, 
end

-- Aufgabe 2b
example (n : ℤ) : n ∣ 0 :=
begin
  -- exact dvd_zero n,
  use 0, simp, 
end

-- Aufgabe 2c
example (k m n: ℤ) (h : k ∣ m) : k ∣ m*n  :=
begin
  -- exact dvd_mul_of_dvd_left h n, 
  cases h with l h1,
  use l*n, 
  rw h1, ring, 
end

-- Aufgabe 2d
example (k m n: ℤ) (h1 : k ∣ m) (h2 : k ∣ n) : k ∣ (m + n)  :=
begin
  -- exact dvd_add h1 h2, 
  cases h1 with l1 h1, 
  cases h2 with l2 h2,
  use l1 + l2, 
  rw [h1, h2], ring,
end

-- Aufgabe 2e
example (n : ℤ) : 0 ∣ n ↔ n = 0 :=
begin
  -- exact zero_dvd_iff, 
  split, 
  intro h, 
  cases h with l h, 
  simp at h, exact h,
  intro h, rw h, 
end

example (k l m n : ℤ) (h₁ : k ∣ m) (h₂ : l ∣ n ) : k*l ∣ m*n :=
begin
  -- exact mul_dvd_mul h₁ h₂, 
  cases h₁ with a h1, 
  cases h₂ with b h2,
  rw [h1, h2],  
  use a*b, ring,
end

-- Aufgabe 2g
example (k l m : ℤ) (h₁ : k ∣ l) (h₂ : l ∣ m) : k ∣ m :=
begin
  -- exact dvd_trans h₁ h₂, 
  cases h₁ with a h1,
  cases h₂ with b h2,
  rw h1 at h2, rw h2, use a*b, ring, 
end

-- Aufgabe 2h
example (m n : ℤ) : (m ∣ n) ↔ (m ∣ -n) :=
begin
  -- exact (dvd_neg m n).symm, 
  split, 
  intro h, cases h with a h, use -a, linarith,  
  intro h, cases h with a h, use -a, linarith,
end

/-
  Es folgen nun drei Aufgaben, die nicht direkt mit library_search gehen, aber fast. 
-/
-- Aufgabe 3a: 
example (k l m n : ℤ) (h₁ : k ∣ l) (h₂ : k ∣ m) (h₃ : k ∣ n) : k ∣ l + m + n :=
begin
  refine dvd_add _ h₃, 
  exact dvd_add h₁ h₂, 
end

-- Aufgabe 3b: 
example (a b k l m n : ℤ) (h₁ : k ∣ l) (h₂ : k ∣ m) : k ∣ l * a + m * b :=
begin
  apply dvd_add, 
  {
    exact dvd_mul_of_dvd_left h₁ a,
  },
  {
    exact dvd_mul_of_dvd_left h₂ b,
  },
end

-- Aufgabe 3c: Hier lernt man etwas über die Implementierung. Die Funktion nat_abs : ℤ → ℕ bildet eine ganze Zahl auf eine natürliche Zahl ab. Hätte man die Funktion abs : ℤ → ℤ verwendet, hätte man ein schwereres Leben, da man auf keine Ergebnisse zurückgreifen kann, die mit Teilbarkeit der natürlichen Zahlen zu tun haben. Schauen Sie doch einmal _dvd_antisymm_ nach!

example ( m n : ℤ ) (h₁ : m ∣ n) (h₂ : n ∣ m) : nat_abs m = nat_abs n :=
begin
  have h1 : nat_abs m  ∣ nat_abs n, exact nat_abs_dvd_iff_dvd.mpr h₁, 
  have h2 : nat_abs n  ∣ nat_abs m, exact nat_abs_dvd_iff_dvd.mpr h₂, 
  apply dvd_antisymm h1 h2, 
end

/- 
  Jetzt kommen wir zu bekannten Teilbarkeitsregeln, allerdings nur in einem begrenzten Zahlenraum. (Allgemeiner geht das in Lean auch, aber dafür bräuchten wir noch etwas mehr Infrastruktur.) Wir beginnen mit der einfachen Aussage, dass eine 4-stellige Zahl genau dann gerade ist, wenn die Einerstelle gerade ist:
-/

-- Aufgabe 4a:
example (a b c d : ℤ) : (2 ∣ (a + 10*b + 100*c + 1000*d)) ↔ (2 ∣ a) :=
begin
  have h1 : 2 ∣ 10 * (b + 10*c + 100*d), use 5 * (b + 10*c + 100*d), ring, 
  split, 
  {
    intro h, 
    have h5 : a = (a + 10 * b + 100 * c + 1000 * d) + (-10)*(b + 10*c + 100*d), ring, 
    rw h5,
    apply dvd_add, 
    assumption, 
    simp, 
    assumption,
  },
  intro h, 
  have h1 : a + 10 * b + 100 * c + 1000 * d = a + (10*(b + 10*c + 100*d)), ring, 
  rw h1, 
  apply dvd_add, 
  assumption,
  assumption,
end

-- Aufgabe 4b:
-- Hier die Aussage, dass eine Zahl genau dann durch 3 teilbar ist, wenn ihre Quersumme durch 3 teilbar ist. 
example (a b c d : ℤ) : (3 ∣ (a + 10*b + 100*c + 1000*d)) ↔ (3 ∣ a + b + c + d) :=
begin
  -- sorry,
  have h1 : 3 ∣ 9 * b + 99*c + 999*d, use 3*b + 33*c + 333*d, ring,
  have h2 : 3 ∣ -9 * b - 99*c - 999*d, use -3*b - 33*c - 333*d, ring,
  split, 
  {  
    intro h, 
    have h3 : a + b + c + d = (a + 10*b + 100*c + 1000*d) + (-9*b- 99*c - 999*d), ring, 
    rw h3, 
    exact dvd_add h h2, 
  },
  {
    intro h, 
    have h3 : a + 10*b + 100*c + 1000*d = (a + b + c + d) + (9*b + 99*c + 999*d), ring,
    rw h3, 
    exact dvd_add h h1, 
  },
end



