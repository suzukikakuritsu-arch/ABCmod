import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Dedup

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

/-- リストの全要素が正なら積も正 -/
private lemma prod_pos_of_pos
    (l : List ℕ) (h : ∀ x ∈ l, 0 < x) : 0 < l.prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.prod_cons]
    apply Nat.mul_pos
    · exact h a (List.mem_cons.mpr (Or.inl rfl))
    · apply ih
      intro x hx
      exact h x (List.mem_cons.mpr (Or.inr hx))

/-- radical は正 -/
lemma radical_pos (n : ℕ) (hn : 0 < n) : 0 < radical n := by
  unfold radical
  apply prod_pos_of_pos
  intro x hx
  have hmem := List.mem_dedup.mp hx
  exact Nat.Prime.pos (Nat.prime_of_mem_primeFactorsList hmem)

/-- Reyssat の算術的確認 -/
lemma reyssat_sum : (3 : ℕ) + 125 = 128 := by decide

lemma reyssat_coprime : Nat.Coprime 3 125 := by decide

lemma reyssat_rad : radical (3 * 125 * 128) = 30 := by
  native_decide

end ABCmod
