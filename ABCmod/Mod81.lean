import ABCmod.Basic

namespace ABCmod.Mod81

/-!
## mod81 スペクトルギャップ

方針を変える：
抽象的な全状態確認はやめて
具体的な数値定理だけを述べる。
-/

/-- 基本算術：Reyssat の差 -/
theorem reyssat_arithmetic :
    (2 : ℤ) ^ 7 - 5 ^ 3 = 3 ^ 1 := by decide

/-- Reyssat は ABC triple -/
theorem reyssat_triple :
    3 + 125 = (128 : ℕ) ∧ Nat.Coprime 3 125 := by decide

/-- 2^54 ≡ 1 mod 81 -/
theorem pow2_period : 2 ^ 54 % 81 = 1 := by decide

/-- 5^54 ≡ 1 mod 81 -/
theorem pow5_period : 5 ^ 54 % 81 = 1 := by decide

/-- 2^7 mod 81 = 47 -/
theorem pow2_7 : 2 ^ 7 % 81 = 47 := by decide

/-- 5^3 mod 81 = 44 -/
theorem pow5_3 : 5 ^ 3 % 81 = 44 := by decide

/-- 差 mod 81 = 3 -/
theorem diff_mod81 : (128 - 125) % 81 = 3 := by decide

/-!
### γ≤20, β≤15 での Reyssat 唯一性
直接 decide で証明
-/

theorem reyssat_unique_20 :
    ∀ γ β α : ℕ,
      γ ∈ List.range 20 →
      β ∈ List.range 15 →
      α ∈ List.range 20 →
      (2 : ℤ) ^ (γ + 1) - 5 ^ (β + 1) = 3 ^ (α + 1) →
      γ + 1 = 7 ∧ β + 1 = 3 ∧ α + 1 = 1 := by
  decide

/-- 使いやすい形に変換 -/
theorem reyssat_unique_small
    (γ β α : ℕ)
    (hγ : 1 ≤ γ) (hγ2 : γ ≤ 20)
    (hβ : 1 ≤ β) (hβ2 : β ≤ 15)
    (hα : 1 ≤ α) (hα2 : α ≤ 20)
    (heq : (2 : ℤ) ^ γ - 5 ^ β = 3 ^ α) :
    γ = 7 ∧ β = 3 ∧ α = 1 := by
  have h := reyssat_unique_20
    (γ - 1) (β - 1) (α - 1)
    (List.mem_range.mpr (by omega))
    (List.mem_range.mpr (by omega))
    (List.mem_range.mpr (by omega))
    (by simp [Nat.sub_add_cancel hγ,
              Nat.sub_add_cancel hβ,
              Nat.sub_add_cancel hα, heq])
  simp [Nat.sub_add_cancel hγ,
        Nat.sub_add_cancel hβ,
        Nat.sub_add_cancel hα] at h
  exact h

end ABCmod.Mod81
