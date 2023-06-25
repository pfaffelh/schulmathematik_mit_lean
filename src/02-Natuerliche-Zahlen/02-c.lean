import tactic -- lade lean-Taktiken
open nat has_dvd

/-
  Ziel dieses Blattes ist es zu zeigen, dass √2 ∉ ℚ. Mit anderen Worten gibt es keine Zahlen m n : ℕ, so dass 2*n^2 = m^2 (zumindest, wenn 0 < m oder 0 < n). Wir werden dies etwas vereinfacht zeigen, indem wir annehmen, dass m und n teilerfremd sind. Als Bonusaufgabe wird es dann noch Punkte geben, wenn wir diese Annahme loswerden. 

  Hier der Beweis, wie man ihn in einem Skript (oder Schulbuch) lesen würde: Seien also m und n teilerfremd. Angenommen 2*n^2 = m^2. Dann wäre also 2 ∣ m^2. Da daher m^2 gerade ist, muss m ebenfalls gerade sein, also m = 2*a für ein a. Damit wäre 2*n^2 = 4 * a^2 oder n^2 = 2 * a^2. Das bedeutet, dass n^2 gerade ist, und wie soeben argumentiert, wäre damit n gerade. Dies widerspricht jedoch der Teilerfremdheit von m und n, da 2 beide Zahlen teilt. 

  Sieht man sich den Beweis an, so brauchen wir:
  a) eine Formlisierung der Teilerfremdheit; 
  b) einen Beweis dafür, dass 2 ∣ m^2 → 2 ∣ m;
  c) einen Beweis der eigentlichen Aussage.
-/

/- a) 
  Um die Teilerfremdheit von m und n zu formalisieren, verwenden wir den größten gemeinsamen Teiler (greatest common divisor, gcd), der in Lean implementiert ist. 
-/

#eval gcd 42 36

/-
  Hier drei einfache Eigenschaften des gcd. 

  theorem gcd_dvd_left (m n : ℕ) : gcd m n ∣ m 

  theorem gcd_dvd_right (m n : ℕ) : gcd m n ∣ n

  theorem dvd_gcd {m n k : ℕ} : k ∣ m → k ∣ n → k ∣ gcd m n 
-/

/-
  b) 
  Wir kommen nun zum Beweis von 2 ∣ m^2 → 2 ∣ m. Wir verwenden hier die Division ( Zeichen /) und den Rest (Źeichen %) der Division zweier natürlicher Zahlen. Es gilt etwa

  mod_add_div : ∀ (a b : ℤ), a % b + b * (a / b) = a
  dvd_iff_mod_eq_zero : ∀ (a b : ℤ), a ∣ b ↔ b % a = 0
  mod_two_eq_zero_or_one (n : ℕ) : n % 2 = 0 ∨ n % 2 = 1 

  Das hier habe ich auch noch gebraucht:

  mul_left_cancel_iff_of_pos [pos_mul_mono_rev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=

-/


-- Aufgabe 1: Hier nun das erste Lemma, dass zeigt, dass gerade und ungerade Zahlen aufeinander folgen.

lemma l1 (m : ℕ) : 2 ∣ m ∨ 2 ∣ (m+1) :=
begin
  sorry,
end

-- Aufgabe 2: Das ist ja fast dieselbe Aussage wie in l1!
lemma l2 (m : ℕ) : 2 ∣ m ↔ ¬(2 ∣ (m+1)) :=
begin
  sorry,
end

/-
  Wir stellen noch zwei Ergebnisse bereit, die eventuell bei Rechnungen helfen:
-/

lemma l3 (m : ℕ) (h : m > 0) : m = m - 1 + 1 :=
begin
  cases m, 
  linarith, 
  simp, 
end

lemma binom3 (n : ℕ) : n*(n+2) = (n+1)^2 - 1 :=
begin
  ring, 
end

-- Aufgabe 3: Hier ist nun die Aussage, die wir eigentlich unter b) zeigen wollten:

lemma l4 (m : ℕ) (h : 2 ∣ m^2 ) : 2 ∣ m :=
begin
  sorry, 
end

/-
  c)
  Aufgabe 4: Nun kommt die eigentliche Aufgabe, nämlich der Beweis der Aussage, dass 2*n^2 = m^2 für alle m n : ℕ, unter der Bedingung gcd m n = 1:
-/

lemma l5 (m n : ℕ) (h_gcd : gcd m n = 1) : 2*m^2 ≠ n^2 :=
begin
  sorry,
end


-- Aufgabe 5 (Bonus): Hier noch die Bonusaufgabe, die darin besteht, die Bedingung gcm m n = 1 loszuwerden. 

/-
  Hier zwei Aussagen, die ich in meiner Lösung gebraucht habe:
  lt_one_iff: ∀ {n : ℕ}, n < 1 ↔ n = 0

  pow_pos : ∀ {α : Type u_1} [_inst_1 : strict_ordered_semiring α] {a : α}, 0 < a → ∀ (n : ℕ), 0 < a ^ n
-/

-- Zuerst müssen sicherstellen, dass gcd m n ≠ 0. Dafür ist dieses Lemma hilfreich: 

lemma l6 (m n : ℕ) (hn : 0 < m ∨ 0 < n) : 0 < gcd m n :=
begin
  sorry,
end

#check l5

-- Hier ist also die Bonusaufgabe
lemma l7 (m n : ℕ) (hn : 0 < n) : 2*m^2 ≠ n^2 :=
begin
  sorry,
end

