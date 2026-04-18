import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Dedup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

namespace ABCmod

/-!
## 基本定義
-/

/-- ABC triple -/
structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  sum   : a + b = c
  cop   : Nat.Coprime a b

/-- radical : 素因数の積（重複なし）-/
def radical (n : ℕ) : ℕ :=
  n.primeFactorsList.dedup.prod

/-- ω : 素因数の個数 -/
def omega (n : ℕ) : ℕ :=
  n.primeFactorsList.dedup.length

/-!
## 基本補題
-/

lemma radical_pos (n : ℕ) (hn : 0 < n) : 0 < radical n := by
  unfold radical
  apply List.prod_pos
  intro p hp
  have := List.mem_dedup.mp hp
  have hprime := Nat.prime_of_mem_primeFactorsList this
  exact Nat.Prime.pos hprime

lemma radical_le (n : ℕ) : radical n ≤ n := by
  unfold radical
  apply Nat.prod_primeFactorsList_dvd |>.symm ▸ le_refl _
  -- 方針：radical n | n → radical n ≤ n
  sorry

lemma radical_dvd (n : ℕ) (hn : 0 < n) : radical n ∣ n := by
  unfold radical
  apply List.prod_dvd_of_mem_primeFactorsList
  · exact List.dedup_sublist _
  · exact Nat.primeFactorsList_prod hn

/-- radical ≥ 2^ω -/
lemma radical_ge_two_pow_omega (n : ℕ) (hn : 1 < n) :
    2 ^ omega n ≤ radical n := by
  unfold radical omega
  apply List.prod_ge_pow_card_of_ge
  · intro p hp
    have := List.mem_dedup.mp hp
    have hprime := Nat.prime_of_mem_primeFactorsList this
    exact hprime.two_le
  · exact List.nodup_dedup _

end ABCmod
