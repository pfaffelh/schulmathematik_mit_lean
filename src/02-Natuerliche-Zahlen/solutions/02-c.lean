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
  -- sorry,
  obtain hm : m = m % 2 + 2 * (m / 2) := (mod_add_div m 2).symm, 
  obtain hm1 : m % 2 = 0 ∨ m % 2 = 1 := mod_two_eq_zero_or_one m,
  cases hm1 with hma hmb, 
  { left, 
    rwa dvd_iff_mod_eq_zero,
  },
  {
    right, 
    obtain h2 : m + 1 = 2 *(1 + (m/2)) := by linarith, 
    use (1 + m/2), assumption,
  },
end

-- Aufgabe 2: Das ist ja fast dieselbe Aussage wie in l1!
lemma l2 (m : ℕ) : 2 ∣ m ↔ ¬(2 ∣ (m+1)) :=
begin
  -- sorry,
  split, 
  {
    intros h h1, 
    rw dvd_iff_mod_eq_zero at *,
    rw add_mod at h1, rw h at h1, 
    simp at h1, 
    exact h1, 
  },
  {
    intro h, 
    cases l1 m with h1 h2, 
    exact h1, 
    exfalso, 
    exact h h2, 
  },
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
  -- sorry, 
  cases m, 
  {
    use 0, 
    simp,
  },
  { 
    by_contra h1,
    rw ← succ_sub_one m at h1, 
    rw ← l2 at h1,
    simp at h1, 
    have h2 : 2 ∣ m*(m+2), 
    {
      cases h1 with a ha, 
      use a * (m+2),
      rw ← mul_assoc, 
      rw ← ha, 
    },
    rw binom3 at h2, 
    apply (l2 ((m + 1) ^ 2 - 1)).1 h2,
    rw ← l3 ((m + 1)^2) _, 
    exact h, 
    exact ne_zero.pos ((m + 1) ^ 2), 
  },
end

/-
  c)
  Aufgabe 4: Nun kommt die eigentliche Aufgabe, nämlich der Beweis der Aussage, dass 2*n^2 = m^2 für alle m n : ℕ, unter der Bedingung gcd m n = 1:
-/

lemma l5 (m n : ℕ) (h_gcd : gcd m n = 1) : 2*m^2 ≠ n^2 :=
begin
  intro h,
  have h1 : 2 ∣ n, 
  { 
    have h : 2 ∣ n^2,
    use m^2, linarith,
    exact l4 n h,  
  },
  have hn := h1, 
  cases h1 with a ha, 
  rw ha at h, 
  obtain h2 : 2*a^2 = m^2 := by linarith, 
  have hm : 2 ∣ m, 
  { 
    have hm : 2 ∣ m^2,
    use a^2, 
    linarith,
    exact l4 m hm,  
  },
  have h4 : 2 ∣ 1, 
  {
    nth_rewrite 1 ← h_gcd, 
    apply dvd_gcd hm hn, 
  },
  obtain h5 : ¬ 2 ∣ 1 :=  by norm_num, 
  exact h5 h4, 
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
  -- sorry,
  by_contra h, 
  simp at h, 
  cases hn;
  linarith, 
end

#check l5

-- Hier ist also die Bonusaufgabe
lemma l7 (m n : ℕ) (hn : 0 < n) : 2*m^2 ≠ n^2 :=
begin
  -- sorry,
  intro h, 
  have hm : 0 < m, 
  {
    by_contra h1,
    simp at h1, 
    rw h1 at h, 
    simp at h, 
    obtain h2 : 0 < n^2 := pow_pos hn 2,
    linarith,   
  },
  let a := gcd m n, 
  obtain ha : 0 < a := l6 m n (or.inr hn), 
  obtain hm1 : a ∣ m := gcd_dvd_left m n, 
  obtain hn1 : a ∣ n := gcd_dvd_right m n, 
  cases hm1 with b hb, 
  cases hn1 with c hc, 
  rw [hb, hc] at h, 
  have h_gcd : gcd b c = 1, 
  {
    by_contra h1, 
    have h2 : gcd b c > 1, 
    {
      by_contra h2, 
      have h3 : gcd b c = 0, 
      push_neg at h2, 
      have h3 : gcd b c < 1, exact ne.lt_of_le h1 h2, 
      exact lt_one_iff.mp h3, 
      have hc2 : c = 0, 
      {
        have h4 : 0 ∣ c, rw ← h3, exact gcd_dvd_right b c,
        cases h4 with d hd, simp at hd, exact hd,  
      },
      rw hc2 at hc, simp at hc, linarith, 
    },
    let d := gcd b c, 
    have hb1 : d ∣ b, exact gcd_dvd_left b c, 
    have hc1 : d ∣ c, exact gcd_dvd_right b c, 
    cases hb1 with e he, 
    cases hc1 with f hf, 
    rw he at hb, 
    rw hf at hc, 
    have hm1 : a*d ∣ m, use e, simp [hb], ring, 
    have hn1 : a*d ∣ n, use f, simp [hc], ring, 
    have h3 : a*d ∣ a, exact dvd_gcd hm1 hn1, 
    have h4 : a < a*d, exact lt_mul_right ha h2,
    exact not_dvd_of_pos_of_lt ha h4 h3,
  },
  {
    obtain h1 : 2* (a*b)^2 = a^2 * (2 * b^2) :=  by ring, 
    obtain h2 : (a*c)^2 = a^2 * c^2 :=  by ring, 
    rw [h1, h2] at h,
    rw mul_left_cancel_iff_of_pos (pow_pos ha 2) at h, 
    revert h, 
    exact l5 b c h_gcd, 
  },
end

