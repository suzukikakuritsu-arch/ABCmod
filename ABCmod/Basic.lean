import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Prod

namespace ABCmod

/-- ABC triple の定義 -/
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

/-- omega' : 素因数の個数 -/
def omega' (n : ℕ) : ℕ :=
  n.primeFactorsList.dedup.length

/-- radical は正 -/
lemma radical_pos (n : ℕ) (hn : 0 < n) : 0 < radical n := by
  unfold radical
  induction n.primeFactorsList.dedup with
  | nil =>
    simp
  | cons p ps ih =>
    simp [List.prod_cons]
    constructor
    · have : p ∈ p :: ps := List.mem_cons_self p ps
      have hmem : p ∈ n.primeFactorsList := by
        have := List.mem_dedup.mp this
        exact this
      exact Nat.Prime.pos (Nat.prime_of_mem_primeFactorsList hmem)
    · exact ih

/-- Reyssat triple の算術的確認 -/
lemma reyssat_sum : (3 : ℕ) + 125 = 128 := by decide

lemma reyssat_coprime : Nat.Coprime 3 125 := by decide

lemma reyssat_rad : radical (3 * 125 * 128) = 30 := by
  native_decide

end ABCmod
