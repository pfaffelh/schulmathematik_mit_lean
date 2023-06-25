import tactic -- lade lean-Taktiken
import data.real.basic
open nat

/-
Wir kommen nun zu den natürlichen Zahlen, und kümmern uns zunächst darum, wie diese in lean implementiert sind. Die entsprechende Definition ist

```
inductive nat
| zero : nat
| succ (n : nat) : nat
notation `ℕ` := nat
```

Das bedeutet: Der Typ nat (oder ℕ) hat den Term zero (oder 0), und wenn n : ℕ dann ist auch succ n : ℕ (wobei succ für successor oder Nachfolger steht.) Eine natürlich Zahl ist also entweder 0 oder Nachfolger einer natürlichen Zahl. Das kann man auch beweisen (mit cases):
-/

example (n : ℕ) : n = 0 ∨ (∃ (k : ℕ), n = succ k) :=
begin
  cases n, 
  {left, 
  refl,},
  {right, use n,}
end

/-
  Aufgabe 1: Versuchen Sie doch mal, dieses Beispiel etwas weiter zu verfolgen. 
  Hier habe ich zwei Lemmas gebraucht (um rw darauf anzuwenden; beim ersten weiß lean, dass α = ℕ die Eigenschaft _has_lt_ hat (wobei lt für _lower than_ steht, d.h. ℕ ist geordnet)):

  gt_iff_lt : ∀ {α : Type} [_inst_1 : has_lt α] {a b : α}, a > b ↔ b < a

  nat.succ_lt_succ_iff : ∀ {m n : ℕ}, m.succ < n.succ ↔ m < n

  Diese und noch viel mehr Aussagen kann man zB auch hier https://leanprover-community.github.io/ finden. Siehe auch noch weiter unten für weitere Beispiele.
-/ 
example (n : ℕ) (h : n > 1) : ∃ (k : ℕ), n = k + 2 :=
begin
  sorry,
end

/-
  Nun kommen wir zu konkreten Rechnungen. Wir haben ja bereits gelernt, wie _rw_ funktioniert. Dies, zusammen mit den vielen Aussage der mathlib, wird uns nun helfen, Rechenaufgaben zu lösen. Dabei bewegen wir uns zunächst im Raum der natürlichen Zahlen. Lemmas, die wir im folgenden verwenden werden, sind etwa die in mathlib abgespeicherten Beweise davon, dass ℕ die Eigenschaften add_zero_class, mul_one_class, add_semigroup, add_comm_semigroup besitzt, sowie die Lemmas: (für die Klammerungen, siehe Skript)

  zero_add : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), 0 + a = a

  add_zero : ∀ {M : Type} [_inst_1 : add_zero_class M] (a : M), a + 0 = a

  one_mul : ∀ {M : Type ?} [_inst_1 : mul_one_class M] (a : M), 1 * a = a

  mul_one : ∀ {M : Type ?} [_inst_1 : mul_one_class M] (a : M), a * 1 = a

  add_assoc : ∀ {G : Type ?} [_inst_1 : add_semigroup G] (a b c : G), a + b + c = a + (b + c)
  
  add_comm : ∀ {G : Type ?} [_inst_1 : add_comm_semigroup G] (a b : G), a + b = b + a
  
  mul_assoc : ∀ {G : Type ?} [_inst_1 : semigroup G] (a b c : G), a * b * c = a * (b * c)
  
  mul_comm : ∀ {G : Type ?} [_inst_1 : comm_semigroup G] (a b : G), a * b = b * a
-/

-- Hier ein Beispiel; wenn Sie mit der Maus etwa über _add_zero_gehen, so zeigt Ihnen vscode die entsprechende Aussage. 
example (m n : ℕ) : m + n = n + m + 0 :=
begin
  rw add_zero, 
  apply add_comm,
  -- oder rw add_comm,
end

/-
  Um bei längeren Rechnungen den Überblick zu behalten, gibt es den _calc_-Modus. Der funktioniert in obigem Beispiel so:
-/

example (m n : ℕ) : m + n = n + m + 0 :=
  begin
  calc m + n = n + m : by { rw add_comm, }
    ...      = n + m + 0 : by { rw add_zero, },
end

/-
  Man lese sich hierzu am besten auch die Beschreibung von _calc_ im Skript durch. 
  
  Außerdem brauchen wir manchmal auch die Taktik _nth_rewrite_ (siehe auch das Skript), wenn wir festlegen wollen, an welcher Stelle wir etwas umschreiben wollen. Siehe das nächste Beispiel. (Versuchen Sie doch mal, das nth_rewrite durch ein rw zu erstzen!) 
-/

lemma double (n : ℕ) : n + n = 2*n :=
begin
  calc n + n = 1 * n + n : by {nth_rewrite 0 ← one_mul n,}
  ... = 1 * n + 1 * n : by {nth_rewrite 1 ← one_mul n,}
  ... = (1 + 1) * n : by {rw add_mul, }
  ... = 2 * n : by {refl, },
end

/-
  Bevor wir nun zu den weiteren Aufgaben kommen, beweisen wir eine binomische Formel: Man beachte, dass jede {} wie ein eigener begin...end-Block funktioniert.
-/

lemma binom1 (n : ℕ) : (n+1)^2 = n^2 + 2*n + 1 :=
begin
   calc (n+1)^2 = (n+1) * (n+1) : by { rw pow_two, }
  ... = (n+1)*n + (n+1) * 1: by {rw mul_add, }
  ... = n*n + 1*n + (n+1) : by {rw add_mul, rw mul_one (n+1),}
  ... = n^2 + n + (n+1) : by {rw one_mul, rw ← pow_two,}
  ... = n^2 + (n + n+1) : by {rw add_assoc, rw ← add_assoc n n 1,}
  ... = n^2 + 2*n + 1 : by { rw ← add_assoc, rw ← double, },
end

/- 
  Hier ein alternativer, aber schlechter lesbarer Beweis:
-/
example (n : ℕ): (n+1)^2 = n^2 + 2*n + 1 :=
begin
  rw [pow_two, mul_add, add_mul, mul_one (n+1), one_mul, ← pow_two,  add_assoc, ← add_assoc n n 1, ← add_assoc, ← double],
end

/-
  Aufgabe 2)
   Formalisieren und beweisen Sie die dritte binomische Formel in der Form n*(n+2) = (n+1)^2 - 1. Verwenden Sie dazu am besten den calc-Modus.
   Hinweis: evtl brauchen Sie das Lemma 

  nat.add_succ_sub_one : ∀ (n m : ℕ), n + m.succ - 1 = n + m
-/

lemma binom3 (n : ℕ) : n*(n+2) = (n+1)^2 - 1 :=
begin
  apply eq.symm,
  sorry,
end

-- Aufgabe 3: Können Sie daraus auch die dritte binomische Formel in der ursprünglichen Form ableiten?
example (n : ℕ) (h : n > 0) : (n-1)*(n+1) = n^2 - 1 :=
begin
  sorry,
end

/-
  Übrigens: Das Umschreiben mit rw von jeder kleinen Rechenregel kann lästig werden. Es gibt vier Taktiken, die hier wesentlich mehr Power haben: 
  
  - ring : kennt alle Rechenregeln in (Halb-)Ringen, also zB den natürlichen Zahle; kann allerdings keine Hypothesen benutzen; löst direkt das Lemma binom1;
  - norm_num : kann mit Zahlen (aber keinen Variablen) rechnen;
  - linarith : kann unter Zuhilfenahme von Hypothesen lineare Gleichungen und Ungleichungen beweisen;
  - simp: in mathlib gibt es viele Lemmas, die der Vereinfachung dienen sollen, also etwa n+0=n. Diese sind immer =- oder ↔-Aussagen und sind dort mit @simp gekennzeichnet. Die simp-Taktik kann auch diese zugreifen.
-/

example (m n : ℕ) : (m + n)^3 = m^3 + 3*m*n^2 + 3*m^2*n + n^3 :=
begin
  ring,
end

example : 123 * 321 = 39483 :=
begin
  norm_num,
end

example (k m n : ℕ) (h1 : k ≤ m+n) (h2 : m < n) : k < 2*n :=
begin
  linarith,
end

example (n : ℕ) : n + 0 + 0 = 0 + 0 + n :=
begin
  simp,
  -- ring geht auch
  -- linarith geht auch
end

/-
  Es folgen ein paar Aufgaben, die mit jeweils einer einzigen Zeile zu lösen sind:
-/

-- Aufgabe 4a
example : 0 < 1 :=
begin
  sorry,
end

-- Aufgabe 4b
example (n : ℕ): n * (n + 1) * (n + 2) = n^3 + 3 * n^2 + 2 * n :=
begin
  sorry,
end

-- Aufgabe 4c
example : 1^100 = 100/100 := 
begin
  sorry,
end

/-
  Aufgabe 5: eine nicht-lineare Ungleichung; übrigens funktioniert der calc-Modus auch für Ungleichungen, also 
  calc n = 1 * n : by {...}
   ... ≤ 2 * n : by {...},
-/
example (n : ℕ) : n ≤ n^2 :=
begin
  sorry,
end


/-
  Es folgen jetzt noch drei Aufgaben mit weniger Hilfestellung. Teil der Aufgabe ist jeweils auch, das entsprechende Resultat zu suchen, mit dem der Beweis einfacher wird!

  Aufgabe 6 : 
-/

example (m n : ℕ) : m^(n+2) = m * m^n * m :=
begin
  sorry,
end

/-
  Aufgabe 7 : 
-/

example (m n : ℕ) : (m + n) * (m - n) = m^2 - n^2 :=
begin
  sorry,
end

/-
  Aufgabe 8 : 
-/

example (k m n : ℕ) (hkm : k ≤ m) (hmn : m ≤ n) : k^2 ≤ n^3 := 
begin
  sorry,
end


